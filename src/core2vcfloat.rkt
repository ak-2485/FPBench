#lang racket

(require "ml.rkt" "fpcore-reader.rkt" "fpcore-extra.rkt" "range-analysis.rkt")
(provide vcfloat-header core->vcfloat vcfloat-supported vcfloat-footer)

(define vcfloat-supported
  (supported-list
    (invert-op-proc
      (curry set-member?
        '(while)))
    fpcore-consts
    (curry set-member? '(binary32 binary64 integer real))
    ieee754-rounding-modes))


(define vcfloat-reserved          ; Language-specific reserved names (avoid name collision)
  '(and as assert begin class constraint do done down to else
    end exception external false for fun function funtor if in
    include inherit initializer land lazy let lor lsl lsr lxor
    match method mod module mutable new nonrec object of open
    or private rec sig struct then to true try type val virtual
    when while with))

(define vcfloat-header (const "From vcfloat Require Import Automate Prune FPLang FPLangOpt RAux Rounding Reify Float_notations.\nRequire Import IntervalFlocq3.Tactic.\nImport Binary List ListNotations.\nSet Bullet Behavior \"Strict Subproofs\".\nSection WITHNANS.\nContext {NANS:Nans}.\nOpen Scope R_scope.\n\n"))

(define vcfloat-footer (const "End WITHNANS.\nClose R_scope."))

(define (fix-name name)
  (apply string-append
    (for/list ([char (~a name)])
      (if (regexp-match #rx"[a-zA-Z0-9_]" (string char))
          (string (char-downcase char))
          (format "_~a_" (char->integer char))))))

(define (equality->vcfloat x xs)
  (format "(~a)"
          (string-join
            (for/list ([a (cons x xs)] [b xs])
              (format "(~a = ~a)" a b))
            " && ")))

(define (inequality->vcfloat x xs)
  (format "(not (~a))"
          (string-join
            (for/list ([a (cons x xs)] [b xs])
              (format "(~a = ~a)" a b))
            " || ")))

(define/match (vcfloat-type->suffix type)
  [("boolean") ""]
  [('binary32) "%F32"]
  [('binary64) "%F64"]
  [("ftype Tdouble") "%F64"]
  [("ftype Tsingle") "%F32"]
  [("Tdouble") "%F64"]
  [("Tsingle") "%F32"]
  [("Z") "%Z"])

(define/match (type->vcfloat type)
  [('binary64) "ftype Tdouble"]
  [('binary32) "ftype Tsingle"]
  [('boolean) "bool"]
  [('integer) "Z"])

(define/match (type->vcfloat-type type)
  [('binary64) "Tdouble"]
  [('binary32) "Tsingle"]
  [('boolean) "bool"]
  [('integer) "Z"])

(define (round->vcfloat x type_to )
  (format "cast ~a _ (~a)" type_to  (trim-infix-parens x)))

(define (round-outer->vcfloat x ctx1 ctx2)
  (define type_to (type->vcfloat-type (ctx-lookup-prop ctx2 ':precision)))
  (format "cast ~a _ (~a)" type_to  x))

(define (round-const->vcfloat x ctx )
  (define type (type->vcfloat-type (ctx-lookup-prop ctx ':precision)))
  (define suffix (vcfloat-type->suffix (ctx-lookup-prop ctx ':precision)))
  (format "cast ~a ~a (~a)~a" type type (trim-infix-parens x) suffix))

(define (operator->vcfloat op args ctx)
  (define type (type->vcfloat (ctx-lookup-prop ctx ':precision)))
  (define type_cast (type->vcfloat-type (ctx-lookup-prop ctx ':precision)))
  (match (cons op args)
   [(list '- a) (format "(-~a)" a)]
   [(list (or '+ '- '* '/) a b) (format "(~a ~a ~a)~a"
      a op b (vcfloat-type->suffix type))]
   [_
    (define args* (string-join args " "))
     (format "(Float.~a ~a)" op args*)]))

(define constant->expr
  (match-lambda
    ['E "exp(1)"]
    ['LN2 "log(2)"]
    ['LN10 "log(10)"]
    ['PI "4 * atan(1)"]
    ['PI_2 "2 * atan(1)"]
    ['PI_4 "atan(1)"]
    ['M_1_PI "1 / (4 * atan(1))"]
    ['M_2_PI "1 / (2 * atan(1))"]
    ['M_2_SQRTPI "1 / sqrt(atan(1))"]
    ['SQRT2 "sqrt(2)"]
    ['SQRT1_2 "1 / sqrt(2)"]
    [(? hex? expr) (format "~a" expr)]
    [(? number? expr) (format-number expr)]
    [c (error 'constant->expr "Unsupported constant ~a" c)]))

(define (constant->vcfloat x ctx)
  (define cexpr (constant->expr x))
  (define type (type->vcfloat-type (ctx-lookup-prop ctx ':precision)))
  (define suffix (vcfloat-type->suffix type))
  (format "(~a)~a" cexpr suffix))

(define (params->vcfloat args arg-ctxs)
  (string-join
    (for/list ([arg (in-list args)] [ctx (in-list arg-ctxs)])
      (let ([type (type->vcfloat (ctx-lookup-prop ctx ':precision))])
        (format "(~a : ~a)" arg type)))
    " "))

(define (params->vcfloat-fun-args args)
  (string-join
    (for/list ([arg (in-list args)])
       (format "~a " arg))
    " "))

(define (body-is-multi-lined? body)
  (or (string-contains? body "if")
      (string-contains? body "let")))

(define (program->vcfloat name args arg-ctxs body ctx)
  (define expr-name
    (let ([name* (ctx-lookup-prop ctx ':name #f)])
      (if name* (let-values ([(_ name) (ctx-unique-name ctx name*)]) name) name)))
  (define pre ((compose canonicalize remove-let)
                (ctx-lookup-prop ctx ':pre 'TRUE)))
  (define var-ranges
    (make-immutable-hash
      (dict-map (condition->range-table pre)
                (lambda (var range) (cons (ctx-lookup-name ctx var) range)))))

  (define arg-strings-bmap
    (for/list ([arg args] [ctx arg-ctxs])
      (define range (dict-ref var-ranges arg (make-interval -inf.0 +inf.0)))
      (define arg-num (+ (index-of args arg) 1))
      (unless (nonempty-bounded? range)
        (error 'vcfloat->function "Bad range for ~a in ~a (~a)" arg name range))
      (unless (= (length range) 1)
        (print range)
        (error 'vcfloat->function "vcfloat only accepts one sampling range"))
      (match-define (interval l u l? u?) (car range))
      (define prec (ctx-lookup-prop ctx ':precision))
      (format "Build_varinfo ~a ~a%positive (~a) (~a)" (type->vcfloat-type prec) arg-num
        (format-number l) (format-number u))))

  (define arg-strings-vmap
    (for/list ([arg args] [ctx arg-ctxs])
      (define arg-num (+ (index-of args arg) 1))
      (define prec (ctx-lookup-prop ctx ':precision))
      (format "(~a%positive, existT ftype ~a ~a)" arg-num (type->vcfloat-type prec) arg)))

  (define arg-strings-reify
    (for/list ([arg args] [ctx arg-ctxs])
      (define arg-num (+ (index-of args arg) 1))
      (format "~a%positive" arg-num )))

  (define var-string-list-reify
    (if (null? arg-strings-bmap)
        ""
        (format "[~a]" (string-join arg-strings-reify ";"))))

  (define var-string-list-bmap
    (if (null? arg-strings-bmap)
        ""
        (format "[~a]" (string-join arg-strings-bmap ";"))))

  (define var-string-list-vmap
    (if (null? arg-strings-vmap)
        ""
        (format "[~a]" (string-join arg-strings-vmap ";"))))

  (define def-string-list-bmap
    (if (non-empty-string? body)
        (format "Definition ~a_bmap_list := ~a.\n" expr-name var-string-list-bmap)
        ""))

  (define def-string-bmap
    (if (non-empty-string? body)
        (format "Definition ~a_bmap :=\n ltac:(let z := compute_PTree (boundsmap_of_list ~a_bmap_list) in exact z).\n" expr-name expr-name)
        ""))

  (define def-string-list-vmap
    (if (non-empty-string? body)
        (format "Definition ~a_vmap_list ~a := ~a.\n" expr-name (params->vcfloat args arg-ctxs) var-string-list-vmap)
        ""))

  (define def-string-vmap
    (if (non-empty-string? body)
        (format "Definition ~a_vmap ~a :=\n ltac:(let z := compute_PTree (valmap_of_list (~a_vmap_list ~a)) in exact z).\n" expr-name (params->vcfloat args arg-ctxs) expr-name (params->vcfloat-fun-args args))
        ""))


  (define def-string
    (if (non-empty-string? body)
        (format "Definition ~a ~a := \n  ~a.\n" expr-name (params->vcfloat args arg-ctxs) body)
        ""))

  (define def-string-expr
    (if (non-empty-string? body)
        (format "Definition ~a_expr := \n ltac:(let e' :=  HO_reify_float_expr constr:(~a) ~a in exact e').\n" expr-name var-string-list-reify expr-name)
        ""))

  (define lemma-string
        (format "Lemma ~a_bound:\n\tfind_and_prove_roundoff_bound ~a_bmap ~a_expr.\nProof.\neexists. intro. prove_roundoff_bound.\n -\ntime \"prove_rndval\" prove_rndval; time \"interval\" interval.\n-\ntime \"prove_roundoff_bound2\" prove_roundoff_bound2;\ntime \"prune_terms\" (prune_terms (cutoff 30)).\ntime \"do_interval\" do_interval.\nDefined.\n" expr-name expr-name expr-name))


  (define bound-string1
    (format "Definition ~a_bound_val := Eval simpl in (proj1_sig ~a_bound)." expr-name expr-name))

  (define bound-string2
    (format "Print ~a_bound_val." expr-name))

  (format "~a\n~a\n~a\n~a\n~a\n~a\n~a\n" def-string-list-bmap def-string-bmap def-string def-string-expr lemma-string bound-string1 bound-string2))


(define-expr-visitor ml-visitor vcfloat-visitor
  [(visit-let_ vtor let_ vars vals body #:ctx ctx)
    (define indent (ctx-lookup-extra ctx 'indent))
    (define ctx*
      (for/fold ([ctx* ctx] #:result ctx*)
                ([var (in-list vars)] [val (in-list vals)])
        (define val-ctx (match let_ ['let ctx] ['let* ctx*]))
        (define-values (name-ctx name)    ; messy workaround to get val context
          (parameterize ([current-output-port (open-output-nowhere)])
            (let-values ([(_ var-ctx) (visit/ctx vtor val val-ctx)])
              (let ([prec (ctx-lookup-prop val-ctx ':precision)])
                (ctx-unique-name ctx* var prec)))))
        (printf "let ~a := " name)
        (define val-ctx* (ctx-update-extra val-ctx 'indent
                                           (curry format "~a~a" double-indent)))
        (printf "~a in\n~a" (let-values ([(val* _) (visit/ctx vtor val val-ctx*)])
                              (trim-infix-parens val*))
                            indent)
        name-ctx))
    (define-values (body* body-ctx) (visit/ctx vtor body ctx*))
    (values body* body-ctx)]

  ; let var = val in
  ; ...
  ; let rec loop vars ... =
  ;   if cond then
  ;     let var = update in
  ;     ...
  ;     loop vars ...
  ;   else
  ;     body
  ; loop inits ...
  [(visit-while_ vtor while_ cond vars inits updates body #:ctx ctx)
    (define indent (ctx-lookup-extra ctx 'indent))
    (define-values (while-ctx fn-name) (ctx-unique-name ctx 'loop))
    (define-values (ctx* vars*)                             ; loop variables
      (for/fold ([ctx* while-ctx] [vars* '()]
                #:result (values ctx* (reverse vars*)))
                ([var (in-list vars)] [val (in-list inits)])
        (define val-ctx (match while_ ['while while-ctx] ['while* ctx*]))
        (define-values (name-ctx name)    ; messy workaround to get val context
          (parameterize ([current-output-port (open-output-nowhere)])
            (let-values ([(_ var-ctx) (visit/ctx vtor val val-ctx)])
              (let ([prec (ctx-lookup-prop val-ctx ':precision)])
                (ctx-unique-name ctx* var prec)))))
        (printf "let ~a := " name)
        (printf "~a in\n~a" (let-values ([(val* _) (visit/ctx vtor val val-ctx)])
                              (trim-infix-parens val*))
                            indent)
        (values name-ctx (cons name vars*))))
    (printf "let rec ~a ~a =\n" fn-name (string-join vars* " "))
    (printf "~a~aif " indent single-indent)
    (define-values (cond* _)          ; condition
      (let ([ctx0 (ctx-update-extra ctx* 'indent (curry format "~a~a" double-indent))])
        (visit/ctx vtor cond ctx0)))
    (printf "~a then\n~a" cond* indent)
    (define-values (ctx** vars**)                           ; loop update
      (for/fold ([ctx** ctx*] [vars* '()] #:result (values ctx** (reverse vars*)))
                ([var (in-list vars)] [val (in-list updates)])
        (define val-ctx (match while_ ['while ctx*] ['while* ctx**]))
        (define-values (name-ctx name)    ; messy workaround to get val context
          (parameterize ([current-output-port (open-output-nowhere)])
            (let-values ([(_ var-ctx) (visit/ctx vtor val val-ctx)])
              (let ([prec (ctx-lookup-prop val-ctx ':precision)])
                (ctx-unique-name ctx** var prec)))))
        (printf "~alet ~a := " double-indent name)
        (define val-ctx*
          (ctx-update-extra val-ctx 'indent
                            (curry format "~a~a~a" double-indent single-indent)))
        (printf "~a in\n~a"
                (let-values ([(val* _) (visit/ctx vtor val val-ctx*)])
                  (trim-infix-parens val*))
                indent)
        (values name-ctx (cons name vars*))))
    (printf "~a~a~a ~a\n" double-indent single-indent fn-name (string-join vars** " "))   ; call the loop
    (printf "~a~aelse\n~a~a" indent single-indent indent double-indent)
    (define-values (body* body-ctx) (visit/ctx vtor body ctx*))
    (printf "~a\n~ain\n" (trim-infix-parens body*) indent)
    (values (format "~a~a ~a" indent fn-name (string-join vars* " "))
            body-ctx)])


(define core->vcfloat
  (make-ml-compiler "vcfloat"
    #:infix-ops (remove* '(+ - * /) default-infix-ops)
    #:operator operator->vcfloat
    #:constant constant->vcfloat
    #:round round-outer->vcfloat
    #:program program->vcfloat
    #:visitor vcfloat-visitor
    #:fix-name fix-name))

(define-compiler '("v") vcfloat-header core->vcfloat vcfloat-footer vcfloat-supported)

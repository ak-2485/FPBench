From vcfloat Require Import Automate FPLang FPLangOpt RAux Rounding Reify Float_notations.
Require Import IntervalFlocq3.Tactic.
Import Binary List ListNotations.
Set Bullet Behavior "Strict Subproofs".
Section WITHNANS.
Context {NANS:Nans}.

Definition matrixdeterminant_bmap_list := [Build_varinfo Tdouble 1%positive (-10) (10);Build_varinfo Tdouble 2%positive (-10) (10);Build_varinfo Tdouble 3%positive (-10) (10);Build_varinfo Tdouble 4%positive (-10) (10);Build_varinfo Tdouble 5%positive (-10) (10);Build_varinfo Tdouble 6%positive (-10) (10);Build_varinfo Tdouble 7%positive (-10) (10);Build_varinfo Tdouble 8%positive (-10) (10);Build_varinfo Tdouble 9%positive (-10) (10)].

Definition matrixdeterminant_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list matrixdeterminant_bmap_list) in exact z).

Definition matrixdeterminant_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b);(3%positive, existT ftype Tdouble c);(4%positive, existT ftype Tdouble d);(5%positive, existT ftype Tdouble e);(6%positive, existT ftype Tdouble f);(7%positive, existT ftype Tdouble g);(8%positive, existT ftype Tdouble h);(9%positive, existT ftype Tdouble i)].

Definition matrixdeterminant_vmap (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (matrixdeterminant_vmap_list a  b  c  d  e  f  g  h  i )) in exact z).

Definition matrixdeterminant (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) :=
  cast Tdouble _ ((((((a * e)%F64 * i)%F64 + ((b * f)%F64 * g)%F64)%F64 + ((c * d)%F64 * h)%F64)%F64 - ((((c * e)%F64 * g)%F64 + ((b * d)%F64 * i)%F64)%F64 + ((a * f)%F64 * h)%F64)%F64)%F64).

Definition matrixdeterminant_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;7%positive;8%positive;9%positive]) matrixdeterminant in exact e').

Definition matrixdeterminant2_bmap_list := [Build_varinfo Tdouble 1%positive (-10) (10);Build_varinfo Tdouble 2%positive (-10) (10);Build_varinfo Tdouble 3%positive (-10) (10);Build_varinfo Tdouble 4%positive (-10) (10);Build_varinfo Tdouble 5%positive (-10) (10);Build_varinfo Tdouble 6%positive (-10) (10);Build_varinfo Tdouble 7%positive (-10) (10);Build_varinfo Tdouble 8%positive (-10) (10);Build_varinfo Tdouble 9%positive (-10) (10)].

Definition matrixdeterminant2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list matrixdeterminant2_bmap_list) in exact z).

Definition matrixdeterminant2_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b);(3%positive, existT ftype Tdouble c);(4%positive, existT ftype Tdouble d);(5%positive, existT ftype Tdouble e);(6%positive, existT ftype Tdouble f);(7%positive, existT ftype Tdouble g);(8%positive, existT ftype Tdouble h);(9%positive, existT ftype Tdouble i)].

Definition matrixdeterminant2_vmap (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (matrixdeterminant2_vmap_list a  b  c  d  e  f  g  h  i )) in exact z).

Definition matrixdeterminant2 (a : ftype Tdouble) (b : ftype Tdouble) (c : ftype Tdouble) (d : ftype Tdouble) (e : ftype Tdouble) (f : ftype Tdouble) (g : ftype Tdouble) (h : ftype Tdouble) (i : ftype Tdouble) :=
  cast Tdouble _ ((((a * (e * i)%F64)%F64 + ((g * (b * f)%F64)%F64 + (c * (d * h)%F64)%F64)%F64)%F64 - ((e * (c * g)%F64)%F64 + ((i * (b * d)%F64)%F64 + (a * (f * h)%F64)%F64)%F64)%F64)%F64).

Definition matrixdeterminant2_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive;7%positive;8%positive;9%positive]) matrixdeterminant2 in exact e').

Definition intro_45_example_45_mixed_bmap_list := [Build_varinfo Tsingle 1%positive (1) (999)].

Definition intro_45_example_45_mixed_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list intro_45_example_45_mixed_bmap_list) in exact z).

Definition intro_45_example_45_mixed_vmap_list (t : ftype Tsingle) := [(1%positive, existT ftype Tsingle t)].

Definition intro_45_example_45_mixed_vmap (t : ftype Tsingle) :=
 ltac:(let z := compute_PTree (valmap_of_list (intro_45_example_45_mixed_vmap_list t )) in exact z).

Definition intro_45_example_45_mixed (t : ftype Tsingle) :=
  cast Tsingle _ (let t_1 := let t1_2 := (t + (1)%F32)%F32 in
      (cast Tdouble _ (t) / cast Tdouble _ (t1_2))%F64 in
  cast Tsingle _ (t_1)).

Definition intro_45_example_45_mixed_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) intro_45_example_45_mixed in exact e').

Definition delta4_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition delta4_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list delta4_bmap_list) in exact z).

Definition delta4_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition delta4_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (delta4_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition delta4 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
  cast Tdouble _ ((((((((-x2) * x3)%F64 - (x1 * x4)%F64)%F64 + (x2 * x5)%F64)%F64 + (x3 * x6)%F64)%F64 - (x5 * x6)%F64)%F64 + (x1 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64)%F64).

Definition delta4_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) delta4 in exact e').

Definition delta_bmap_list := [Build_varinfo Tdouble 1%positive (4) (63504e-4);Build_varinfo Tdouble 2%positive (4) (63504e-4);Build_varinfo Tdouble 3%positive (4) (63504e-4);Build_varinfo Tdouble 4%positive (4) (63504e-4);Build_varinfo Tdouble 5%positive (4) (63504e-4);Build_varinfo Tdouble 6%positive (4) (63504e-4)].

Definition delta_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list delta_bmap_list) in exact z).

Definition delta_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition delta_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (delta_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition delta (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
  cast Tdouble _ (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 + (((-x2) * x3)%F64 * x4)%F64)%F64 + (((-x1) * x3)%F64 * x5)%F64)%F64 + (((-x1) * x2)%F64 * x6)%F64)%F64 + (((-x4) * x5)%F64 * x6)%F64)%F64).

Definition delta_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) delta in exact e').

Definition x_by_xy_bmap_list := [Build_varinfo Tsingle 1%positive (1) (4);Build_varinfo Tsingle 2%positive (1) (4)].

Definition x_by_xy_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list x_by_xy_bmap_list) in exact z).

Definition x_by_xy_vmap_list (x : ftype Tsingle) (y : ftype Tsingle) := [(1%positive, existT ftype Tsingle x);(2%positive, existT ftype Tsingle y)].

Definition x_by_xy_vmap (x : ftype Tsingle) (y : ftype Tsingle) :=
 ltac:(let z := compute_PTree (valmap_of_list (x_by_xy_vmap_list x  y )) in exact z).

Definition x_by_xy (x : ftype Tsingle) (y : ftype Tsingle) :=
  cast Tsingle _ ((x / (x + y)%F32)%F32).

Definition x_by_xy_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) x_by_xy in exact e').

Definition sum_bmap_list := [Build_varinfo Tdouble 1%positive (1) (2);Build_varinfo Tdouble 2%positive (1) (2);Build_varinfo Tdouble 3%positive (1) (2)].

Definition sum_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list sum_bmap_list) in exact z).

Definition sum_vmap_list (x0 : ftype Tdouble) (x1 : ftype Tdouble) (x2 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x0);(2%positive, existT ftype Tdouble x1);(3%positive, existT ftype Tdouble x2)].

Definition sum_vmap (x0 : ftype Tdouble) (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (sum_vmap_list x0  x1  x2 )) in exact z).

Definition sum (x0 : ftype Tdouble) (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
  cast Tdouble _ (let p0 := ((x0 + x1)%F64 - x2)%F64 in
  let p1 := ((x1 + x2)%F64 - x0)%F64 in
  let p2 := ((x2 + x0)%F64 - x1)%F64 in
  ((p0 + p1)%F64 + p2)%F64).

Definition sum_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) sum in exact e').

Definition nonlin1_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition nonlin1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list nonlin1_bmap_list) in exact z).

Definition nonlin1_vmap_list (z : ftype Tdouble) := [(1%positive, existT ftype Tdouble z)].

Definition nonlin1_vmap (z : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (nonlin1_vmap_list z )) in exact z).

Definition nonlin1 (z : ftype Tdouble) :=
  cast Tdouble _ ((z / (z + (1)%F64)%F64)%F64).

Definition nonlin1_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) nonlin1 in exact e').

Definition nonlin2_bmap_list := [Build_varinfo Tdouble 1%positive (1001e-3) (2);Build_varinfo Tdouble 2%positive (1001e-3) (2)].

Definition nonlin2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list nonlin2_bmap_list) in exact z).

Definition nonlin2_vmap_list (x : ftype Tdouble) (y : ftype Tdouble) := [(1%positive, existT ftype Tdouble x);(2%positive, existT ftype Tdouble y)].

Definition nonlin2_vmap (x : ftype Tdouble) (y : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (nonlin2_vmap_list x  y )) in exact z).

Definition nonlin2 (x : ftype Tdouble) (y : ftype Tdouble) :=
  cast Tdouble _ (let t := (x * y)%F64 in
  ((t - (1)%F64)%F64 / ((t * t)%F64 - (1)%F64)%F64)%F64).

Definition nonlin2_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) nonlin2 in exact e').

Definition himmilbeau_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-5) (5)].

Definition himmilbeau_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list himmilbeau_bmap_list) in exact z).

Definition himmilbeau_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2)].

Definition himmilbeau_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (himmilbeau_vmap_list x1  x2 )) in exact z).

Definition himmilbeau (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
  cast Tdouble _ (let a := (((x1 * x1)%F64 + x2)%F64 - (11)%F64)%F64 in
  let b := ((x1 + (x2 * x2)%F64)%F64 - (7)%F64)%F64 in
  ((a * a)%F64 + (b * b)%F64)%F64).

Definition himmilbeau_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) himmilbeau in exact e').

Definition kepler0_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition kepler0_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler0_bmap_list) in exact z).

Definition kepler0_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition kepler0_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (kepler0_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition kepler0 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
  cast Tdouble _ ((((((x2 * x5)%F64 + (x3 * x6)%F64)%F64 - (x2 * x3)%F64)%F64 - (x5 * x6)%F64)%F64 + (x1 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64)%F64).

Definition kepler0_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) kepler0 in exact e').

Definition kepler1_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2)].

Definition kepler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler1_bmap_list) in exact z).

Definition kepler1_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4)].

Definition kepler1_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (kepler1_vmap_list x1  x2  x3  x4 )) in exact z).

Definition kepler1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) :=
  cast Tdouble _ (((((((((x1 * x4)%F64 * ((((-x1) + x2)%F64 + x3)%F64 - x4)%F64)%F64 + (x2 * (((x1 - x2)%F64 + x3)%F64 + x4)%F64)%F64)%F64 + (x3 * (((x1 + x2)%F64 - x3)%F64 + x4)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - (x1 * x3)%F64)%F64 - (x1 * x2)%F64)%F64 - x4)%F64).

Definition kepler1_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive]) kepler1 in exact e').

Definition kepler2_bmap_list := [Build_varinfo Tdouble 1%positive (4) (636e-2);Build_varinfo Tdouble 2%positive (4) (636e-2);Build_varinfo Tdouble 3%positive (4) (636e-2);Build_varinfo Tdouble 4%positive (4) (636e-2);Build_varinfo Tdouble 5%positive (4) (636e-2);Build_varinfo Tdouble 6%positive (4) (636e-2)].

Definition kepler2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list kepler2_bmap_list) in exact z).

Definition kepler2_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3);(4%positive, existT ftype Tdouble x4);(5%positive, existT ftype Tdouble x5);(6%positive, existT ftype Tdouble x6)].

Definition kepler2_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (kepler2_vmap_list x1  x2  x3  x4  x5  x6 )) in exact z).

Definition kepler2 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) (x4 : ftype Tdouble) (x5 : ftype Tdouble) (x6 : ftype Tdouble) :=
  cast Tdouble _ (((((((((x1 * x4)%F64 * ((((((-x1) + x2)%F64 + x3)%F64 - x4)%F64 + x5)%F64 + x6)%F64)%F64 + ((x2 * x5)%F64 * (((((x1 - x2)%F64 + x3)%F64 + x4)%F64 - x5)%F64 + x6)%F64)%F64)%F64 + ((x3 * x6)%F64 * (((((x1 + x2)%F64 - x3)%F64 + x4)%F64 + x5)%F64 - x6)%F64)%F64)%F64 - ((x2 * x3)%F64 * x4)%F64)%F64 - ((x1 * x3)%F64 * x5)%F64)%F64 - ((x1 * x2)%F64 * x6)%F64)%F64 - ((x4 * x5)%F64 * x6)%F64)%F64).

Definition kepler2_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive;4%positive;5%positive;6%positive]) kepler2 in exact e').

Definition intro_45_example_bmap_list := [Build_varinfo Tdouble 1%positive (0) (999)].

Definition intro_45_example_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list intro_45_example_bmap_list) in exact z).

Definition intro_45_example_vmap_list (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble t)].

Definition intro_45_example_vmap (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (intro_45_example_vmap_list t )) in exact z).

Definition intro_45_example (t : ftype Tdouble) :=
  cast Tdouble _ ((t / (t + (1)%F64)%F64)%F64).

Definition intro_45_example_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) intro_45_example in exact e').

Definition sec4_45_example_bmap_list := [Build_varinfo Tdouble 1%positive (1001e-3) (2);Build_varinfo Tdouble 2%positive (1001e-3) (2)].

Definition sec4_45_example_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list sec4_45_example_bmap_list) in exact z).

Definition sec4_45_example_vmap_list (x : ftype Tdouble) (y : ftype Tdouble) := [(1%positive, existT ftype Tdouble x);(2%positive, existT ftype Tdouble y)].

Definition sec4_45_example_vmap (x : ftype Tdouble) (y : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (sec4_45_example_vmap_list x  y )) in exact z).

Definition sec4_45_example (x : ftype Tdouble) (y : ftype Tdouble) :=
  cast Tdouble _ (let t := (x * y)%F64 in
  ((t - (1)%F64)%F64 / ((t * t)%F64 - (1)%F64)%F64)%F64).

Definition sec4_45_example_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) sec4_45_example in exact e').

Definition rump_39_s_32_example_44__32_from_32_c_32_program_bmap_list := [Build_varinfo Tdouble 1%positive (0) (77617);Build_varinfo Tdouble 2%positive (0) (33096)].

Definition rump_39_s_32_example_44__32_from_32_c_32_program_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rump_39_s_32_example_44__32_from_32_c_32_program_bmap_list) in exact z).

Definition rump_39_s_32_example_44__32_from_32_c_32_program_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b)].

Definition rump_39_s_32_example_44__32_from_32_c_32_program_vmap (a : ftype Tdouble) (b : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (rump_39_s_32_example_44__32_from_32_c_32_program_vmap_list a  b )) in exact z).

Definition rump_39_s_32_example_44__32_from_32_c_32_program (a : ftype Tdouble) (b : ftype Tdouble) :=
  cast Tdouble _ (let b2 := (b * b)%F64 in
  let b4 := (b2 * b2)%F64 in
  let b6 := (b4 * b2)%F64 in
  let b8 := (b4 * b4)%F64 in
  let a2 := (a * a)%F64 in
  let firstexpr := ((((((11)%F64 * a2)%F64 * b2)%F64 - b6)%F64 - ((121)%F64 * b4)%F64)%F64 - (2)%F64)%F64 in
  (((((33375e-2)%F64 * b6)%F64 + (a2 * firstexpr)%F64)%F64 + ((55e-1)%F64 * b8)%F64)%F64 + (a / ((2)%F64 * b)%F64)%F64)%F64).

Definition rump_39_s_32_example_44__32_from_32_c_32_program_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) rump_39_s_32_example_44__32_from_32_c_32_program in exact e').

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bmap_list := [Build_varinfo Tdouble 1%positive (0) (77617);Build_varinfo Tdouble 2%positive (0) (33096)].

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_bmap_list) in exact z).

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_vmap_list (a : ftype Tdouble) (b : ftype Tdouble) := [(1%positive, existT ftype Tdouble a);(2%positive, existT ftype Tdouble b)].

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_vmap (a : ftype Tdouble) (b : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_vmap_list a  b )) in exact z).

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point (a : ftype Tdouble) (b : ftype Tdouble) :=
  cast Tdouble _ (let b2 := (b * b)%F64 in
  let b4 := (b2 * b2)%F64 in
  let b6 := (b4 * b2)%F64 in
  let b8 := (b4 * b4)%F64 in
  let a2 := (a * a)%F64 in
  let firstexpr := (((((11)%F64 * a2)%F64 * b2)%F64 - ((121)%F64 * b4)%F64)%F64 - (2)%F64)%F64 in
  ((((((33375e-2)%F64 - a2)%F64 * b6)%F64 + (a2 * firstexpr)%F64)%F64 + ((55e-1)%F64 * b8)%F64)%F64 + (a / ((2)%F64 * b)%F64)%F64)%F64).

Definition rump_39_s_32_example_32_revisited_32_for_32_floating_32_point_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) rump_39_s_32_example_32_revisited_32_for_32_floating_32_point in exact e').

Definition doppler1_bmap_list := [Build_varinfo Tdouble 1%positive (-100) (100);Build_varinfo Tdouble 2%positive (20) (2e4);Build_varinfo Tdouble 3%positive (-30) (50)].

Definition doppler1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler1_bmap_list) in exact z).

Definition doppler1_vmap_list (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble u);(2%positive, existT ftype Tdouble v);(3%positive, existT ftype Tdouble t)].

Definition doppler1_vmap (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (doppler1_vmap_list u  v  t )) in exact z).

Definition doppler1 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
  cast Tdouble _ (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler1_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) doppler1 in exact e').

Definition doppler2_bmap_list := [Build_varinfo Tdouble 1%positive (-125) (125);Build_varinfo Tdouble 2%positive (15) (25000);Build_varinfo Tdouble 3%positive (-40) (60)].

Definition doppler2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler2_bmap_list) in exact z).

Definition doppler2_vmap_list (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble u);(2%positive, existT ftype Tdouble v);(3%positive, existT ftype Tdouble t)].

Definition doppler2_vmap (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (doppler2_vmap_list u  v  t )) in exact z).

Definition doppler2 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
  cast Tdouble _ (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler2_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) doppler2 in exact e').

Definition doppler3_bmap_list := [Build_varinfo Tdouble 1%positive (-30) (120);Build_varinfo Tdouble 2%positive (320) (20300);Build_varinfo Tdouble 3%positive (-50) (30)].

Definition doppler3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list doppler3_bmap_list) in exact z).

Definition doppler3_vmap_list (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) := [(1%positive, existT ftype Tdouble u);(2%positive, existT ftype Tdouble v);(3%positive, existT ftype Tdouble t)].

Definition doppler3_vmap (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (doppler3_vmap_list u  v  t )) in exact z).

Definition doppler3 (u : ftype Tdouble) (v : ftype Tdouble) (t : ftype Tdouble) :=
  cast Tdouble _ (let t1 := ((3314e-1)%F64 + ((6e-1)%F64 * t)%F64)%F64 in
  (((-t1) * v)%F64 / ((t1 + u)%F64 * (t1 + u)%F64)%F64)%F64).

Definition doppler3_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) doppler3 in exact e').

Definition rigidbody1_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition rigidbody1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rigidbody1_bmap_list) in exact z).

Definition rigidbody1_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3)].

Definition rigidbody1_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (rigidbody1_vmap_list x1  x2  x3 )) in exact z).

Definition rigidbody1 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) :=
  cast Tdouble _ (((((-(x1 * x2)%F64) - (((2)%F64 * x2)%F64 * x3)%F64)%F64 - x1)%F64 - x3)%F64).

Definition rigidbody1_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) rigidbody1 in exact e').

Definition rigidbody2_bmap_list := [Build_varinfo Tdouble 1%positive (-15) (15);Build_varinfo Tdouble 2%positive (-15) (15);Build_varinfo Tdouble 3%positive (-15) (15)].

Definition rigidbody2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list rigidbody2_bmap_list) in exact z).

Definition rigidbody2_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2);(3%positive, existT ftype Tdouble x3)].

Definition rigidbody2_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (rigidbody2_vmap_list x1  x2  x3 )) in exact z).

Definition rigidbody2 (x1 : ftype Tdouble) (x2 : ftype Tdouble) (x3 : ftype Tdouble) :=
  cast Tdouble _ (((((((((2)%F64 * x1)%F64 * x2)%F64 * x3)%F64 + (((3)%F64 * x3)%F64 * x3)%F64)%F64 - (((x2 * x1)%F64 * x2)%F64 * x3)%F64)%F64 + (((3)%F64 * x3)%F64 * x3)%F64)%F64 - x2)%F64).

Definition rigidbody2_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) rigidbody2 in exact e').

Definition jetengine_bmap_list := [Build_varinfo Tdouble 1%positive (-5) (5);Build_varinfo Tdouble 2%positive (-20) (5)].

Definition jetengine_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list jetengine_bmap_list) in exact z).

Definition jetengine_vmap_list (x1 : ftype Tdouble) (x2 : ftype Tdouble) := [(1%positive, existT ftype Tdouble x1);(2%positive, existT ftype Tdouble x2)].

Definition jetengine_vmap (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (jetengine_vmap_list x1  x2 )) in exact z).

Definition jetengine (x1 : ftype Tdouble) (x2 : ftype Tdouble) :=
  cast Tdouble _ (let t := (((((3)%F64 * x1)%F64 * x1)%F64 + ((2)%F64 * x2)%F64)%F64 - x1)%F64 in
  let t_42_ := (((((3)%F64 * x1)%F64 * x1)%F64 - ((2)%F64 * x2)%F64)%F64 - x1)%F64 in
  let d := ((x1 * x1)%F64 + (1)%F64)%F64 in
  let s := (t / d)%F64 in
  let s_42_ := (t_42_ / d)%F64 in
  (x1 + ((((((((((2)%F64 * x1)%F64 * s)%F64 * (s - (3)%F64)%F64)%F64 + ((x1 * x1)%F64 * (((4)%F64 * s)%F64 - (6)%F64)%F64)%F64)%F64 * d)%F64 + ((((3)%F64 * x1)%F64 * x1)%F64 * s)%F64)%F64 + ((x1 * x1)%F64 * x1)%F64)%F64 + x1)%F64 + ((3)%F64 * s_42_)%F64)%F64)%F64).

Definition jetengine_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive]) jetengine in exact e').

Definition turbine1_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine1_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine1_bmap_list) in exact z).

Definition turbine1_vmap_list (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := [(1%positive, existT ftype Tdouble v);(2%positive, existT ftype Tdouble w);(3%positive, existT ftype Tdouble r)].

Definition turbine1_vmap (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (turbine1_vmap_list v  w  r )) in exact z).

Definition turbine1 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
  cast Tdouble _ (((((3)%F64 + ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((3)%F64 - ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (45e-1)%F64)%F64).

Definition turbine1_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine1 in exact e').

Definition turbine2_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine2_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine2_bmap_list) in exact z).

Definition turbine2_vmap_list (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := [(1%positive, existT ftype Tdouble v);(2%positive, existT ftype Tdouble w);(3%positive, existT ftype Tdouble r)].

Definition turbine2_vmap (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (turbine2_vmap_list v  w  r )) in exact z).

Definition turbine2 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
  cast Tdouble _ (((((6)%F64 * v)%F64 - ((((5e-1)%F64 * v)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (25e-1)%F64)%F64).

Definition turbine2_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine2 in exact e').

Definition turbine3_bmap_list := [Build_varinfo Tdouble 1%positive (-45e-1) (-3e-1);Build_varinfo Tdouble 2%positive (4e-1) (9e-1);Build_varinfo Tdouble 3%positive (38e-1) (78e-1)].

Definition turbine3_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list turbine3_bmap_list) in exact z).

Definition turbine3_vmap_list (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) := [(1%positive, existT ftype Tdouble v);(2%positive, existT ftype Tdouble w);(3%positive, existT ftype Tdouble r)].

Definition turbine3_vmap (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (turbine3_vmap_list v  w  r )) in exact z).

Definition turbine3 (v : ftype Tdouble) (w : ftype Tdouble) (r : ftype Tdouble) :=
  cast Tdouble _ (((((3)%F64 - ((2)%F64 / (r * r)%F64)%F64)%F64 - ((((125e-3)%F64 * ((1)%F64 + ((2)%F64 * v)%F64)%F64)%F64 * (((w * w)%F64 * r)%F64 * r)%F64)%F64 / ((1)%F64 - v)%F64)%F64)%F64 - (5e-1)%F64)%F64).

Definition turbine3_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive;2%positive;3%positive]) turbine3 in exact e').

Definition verhulst_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition verhulst_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list verhulst_bmap_list) in exact z).

Definition verhulst_vmap_list (x : ftype Tdouble) := [(1%positive, existT ftype Tdouble x)].

Definition verhulst_vmap (x : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (verhulst_vmap_list x )) in exact z).

Definition verhulst (x : ftype Tdouble) :=
  cast Tdouble _ (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  ((r * x)%F64 / ((1)%F64 + (x / k)%F64)%F64)%F64).

Definition verhulst_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) verhulst in exact e').

Definition predatorprey_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (3e-1)].

Definition predatorprey_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list predatorprey_bmap_list) in exact z).

Definition predatorprey_vmap_list (x : ftype Tdouble) := [(1%positive, existT ftype Tdouble x)].

Definition predatorprey_vmap (x : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (predatorprey_vmap_list x )) in exact z).

Definition predatorprey (x : ftype Tdouble) :=
  cast Tdouble _ (let r := (4)%F64 in
  let k := (111e-2)%F64 in
  (((r * x)%F64 * x)%F64 / ((1)%F64 + ((x / k)%F64 * (x / k)%F64)%F64)%F64)%F64).

Definition predatorprey_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) predatorprey in exact e').

Definition carbongas_bmap_list := [Build_varinfo Tdouble 1%positive (1e-1) (5e-1)].

Definition carbongas_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list carbongas_bmap_list) in exact z).

Definition carbongas_vmap_list (v : ftype Tdouble) := [(1%positive, existT ftype Tdouble v)].

Definition carbongas_vmap (v : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (carbongas_vmap_list v )) in exact z).

Definition carbongas (v : ftype Tdouble) :=
  cast Tdouble _ (let p := (35e6)%F64 in
  let a := (401e-3)%F64 in
  let b := (427e-7)%F64 in
  let t := (300)%F64 in
  let n := (1000)%F64 in
  let k := (13806503e-30)%F64 in
  (((p + ((a * (n / v)%F64)%F64 * (n / v)%F64)%F64)%F64 * (v - (n * b)%F64)%F64)%F64 - ((k * n)%F64 * t)%F64)%F64).

Definition carbongas_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) carbongas in exact e').

Definition sqroot_bmap_list := [Build_varinfo Tdouble 1%positive (0) (1)].

Definition sqroot_bmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list sqroot_bmap_list) in exact z).

Definition sqroot_vmap_list (x : ftype Tdouble) := [(1%positive, existT ftype Tdouble x)].

Definition sqroot_vmap (x : ftype Tdouble) :=
 ltac:(let z := compute_PTree (valmap_of_list (sqroot_vmap_list x )) in exact z).

Definition sqroot (x : ftype Tdouble) :=
  cast Tdouble _ ((((((1)%F64 + ((5e-1)%F64 * x)%F64)%F64 - (((125e-3)%F64 * x)%F64 * x)%F64)%F64 + ((((625e-4)%F64 * x)%F64 * x)%F64 * x)%F64)%F64 - (((((390625e-7)%F64 * x)%F64 * x)%F64 * x)%F64 * x)%F64)%F64).

Definition sqroot_expr :=
 ltac:(let e' :=  HO_reify_float_expr constr:([1%positive]) sqroot in exact e').

End WITHNANS.

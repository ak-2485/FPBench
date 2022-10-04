
z = float<ieee_64,ne>(Mz);

Mex1 = (Mz / (Mz + 1));

ex1 float<ieee_64,ne>= (z / (z + float<ieee_64,ne>(1)));

{ ((Mz >= 0) /\ (Mz <= 999)) /\ (Mz in [0, 999])
  -> |ex1 - Mex1| in ? }



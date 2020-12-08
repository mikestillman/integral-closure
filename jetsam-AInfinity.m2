-*
burkeData(Ring,Module,ZZ) := List => (R,M,n) ->(
--currently (11/26) 
--F = burkeData(R,M,6) 
--produces the list of the free modules indexed 0..n in the Burke resolution,
--in a form that things like F_5^[{3,2,0}] work (this is the projection).
--Output is a list of labeled complexes of R-modules
S := ring presentation R;
RS := map(R,S);
MS := pushForward(RS,M);
G := labeledTensorComplex freeResolution(MS, LengthLimit => n);
A' := freeResolution (coker presentation R, LengthLimit => n-1);
A'' := labeledTensorComplex(R**A'[-1]);
A := A''[1];
B0 := complex(apply(length A-1, i-> A.dd_(i+2)))[-2];
BB := {G}|apply(n//2, i->labeledTensorComplex(toList(i+1:B0)|{G}));
C := apply(n+1, i-> select(apply(BB,b-> b_i), c -> c != 0));
apply(C, c -> labeledDirectSum c)
    )
*-

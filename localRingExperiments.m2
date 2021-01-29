
load "Linkage.m2"


--this is from CompleteIntersectionResolutions.m2
makeHomotopies1 (Matrix, ChainComplex, ZZ) := (f,F,b) ->(
     --given a 1 x lenf matrix f and a chain complex 
     -- F_min <-...,
     --the script attempts to make a family of first homotopies
     --on F for the elements of f.
     --The output is a hash table {{J,i}=>s), where
     --J is an integer 0 <= J < lenf, 
     --min F <= i < b
     --and s is a map F_i->F_(i+1) satisfying the conditions
     -- ds_{i}+s_{i}d = f_i. 
     -- if the given b is > max F, then b is replaced by max F.
     S := ring f;
     flist := flatten entries f;
     degs := apply(flist, fi -> degree fi); -- list of degrees (each is a list)
     

     minF := min F;
     maxF := max F;
     if b>max F then b=maxF;

     rem := 0;
     h := null;
     H := new MutableHashTable;          

     --make the initial homotopies from F_minF 0.
     scan(#flist, j->H#{j,minF-1}= map(F_minF, F_(minF-1), 0));

     --now compute the rest of the homotopies. Note that the grading is not yet right
     for i from minF to b do
	       scan(#flist, j->(
		       
u := -H#{j,i-1}*F.dd_i+flist_j*id_(F_i)	;
v :=  F.dd_(i+1);	       
h = u//v;
assert(u == v*h);


-- --	       (h,rem) = 
-- --	          quotientRemainder(-H#{j,i-1}*F.dd_i+flist_j*id_(F_i),
-- 		                   F.dd_(i+1));
-- 	       if rem != 0 then (
-- 		     <<"homotopy " <<{j,i} <<" doesn't exist."<<endl;
-- 		     );



	       H#{j,i} = h));    
	       
     --fix the grading and return a HashTable:
     H1 := hashTable apply(keys H, k->
     {k, map(F_(k_1+1), 
	     tensorWithComponents(S^{-degs_(k_0)},F_(k_1)), 
				         H#k)});
     H1
     )

end--
restart
load "localRingExperiments.m2"
S = ZZ/101[x,y,z]

I = monomialIdeal(x^3,x^2*y,x*y^2,y^3,x*z^2,z^3)
cvw I

I1 = generalLink I
I' = generalLink generalLink I
isHomogeneous I'

I' = ideal(y*z^2-40*z^3+18*x*y-y^2+37*x*z-5*y*z+7*z^2,x*z^2-43*z^3+32*x^2-50*x*y-45*y^2-21*x*z-50*y*z-49*z^2,y^2
     *z-32*z^3-17*x*y-3*y^2+6*x*z+38*y*z+40*z^2,x*y*z-2*z^3-48*x^2+40*x*y+22*y^2-40*x*z+46*y*z+3*z^2,x^2*z+43*z^
     3-17*x^2+42*x*y+17*y^2-43*x*z+3*y*z+14*z^2,y^3-21*z^3-7*x*y+41*y^2-45*x*z+32*y*z-30*z^2,x*y^2-24*z^3+16*x^2
     +47*x*y-30*y^2-47*x*z+44*y*z-43*z^2,x^2*y-14*z^3+42*x^2+11*y^2+17*x*z-5*y*z+22*z^2,x^3-4*x^2+3*x*y+45*y^2-
     12*x*z+26*y*z-46*z^2)
needsPackage "LocalRings"

S' = localRing(S,ideal vars S)
I'=sub(I', S')
netList I'_*
mingens I'
F = res I'
F.dd
makeHomotopies1(mingens I', F)
code methods makeHomotopies1
gb I'
errorDepth = 0
viewHelp LocalRings
viewHelp "LocalRing"

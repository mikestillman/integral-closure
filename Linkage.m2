needsPackage "StableResidual"
needsPackage "MonomialOrbits"
needsPackage "DGAlgebras"
needsPackage "LocalRings"
needsPackage "AInfinity"
needsPackage "CompleteIntersectionResolutions"
--help MonomialOrbits

clkw = method()
clkw Ring := kk  -> (
R := kk[x_12,x_13,x_14,x_23,x_24,x_34,y_12,y_13,y_14,y_23,y_24,y_34,z_123,z_124,z_134,z_234];
M := matrix{{x_12,x_13,x_14,x_23,x_24,x_34},{y_12,y_13,y_14,y_23,y_24,y_34}};
l1 := det(M^{0,1}_{4,1})-det(M^{0,1}_{2,3})-det(M^{0,1}_{5,0});
l2 := det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})-det(M^{0,1}_{5,0});
l3 := -det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})+det(M^{0,1}_{5,0});
l4 := det(M^{0,1}_{1,4})-det(M^{0,1}_{2,3})-det(M^{0,1}_{0,5});
q1 := z_123*l1+2*z_124*(det(M^{0,1}_{1,3}))-2*z_134*det(M^{0,1}_{0,3})+2*z_234*det(M^{0,1}_{0,1});
q2 := -2*z_123*(det(M^{0,1}_{2,4}))+z_124*l2-2*z_134*det(M^{0,1}_{0,4})+2*z_234*det(M^{0,1}_{0,2});
q3 := -2*z_123*det(M^{0,1}_{2,5})+2*z_124*det(M^{0,1}_{1,5})+z_134*l3+2*z_234*det(M^{0,1}_{1,2});
q4 := -2*z_123*det(M^{0,1}_{4,5})+2*z_124*det(M^{0,1}_{3,5})-2*z_134*det(M^{0,1}_{3,4})+z_234*l4;
a := x_12*x_34-x_13*x_24+x_14*x_23;
b := x_12*y_34-x_13*y_24+x_14*y_23+x_34*y_12-x_24*y_13+x_23*y_14;
c := y_12*y_34-y_13*y_24+y_14*y_23;
u := b^2-4*a*c;
ideal(q1,q2,q3,q4,u))

------------------------------------------------------------------------------------------------- Deformed ideal J(t)
clkw' = method()
clkw' Ring := kk -> (
R := kk[x_12,x_13,x_14,x_23,x_24,x_34,y_12,y_13,y_14,y_23,y_24,y_34,z_123,z_124,z_134,z_234,t];
M := matrix{{x_12,x_13,x_14,x_23,x_24,x_34},{y_12,y_13,y_14,y_23,y_24,y_34}};
l1 := det(M^{0,1}_{4,1})-det(M^{0,1}_{2,3})-det(M^{0,1}_{5,0});
l2 := det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})-det(M^{0,1}_{5,0});
l3 := -det(M^{0,1}_{1,4})-det(M^{0,1}_{3,2})+det(M^{0,1}_{5,0});
l4 := det(M^{0,1}_{1,4})-det(M^{0,1}_{2,3})-det(M^{0,1}_{0,5});
q1 := z_123*l1+2*z_124*(det(M^{0,1}_{1,3}))-2*z_134*det(M^{0,1}_{0,3})+2*z_234*det(M^{0,1}_{0,1});
q2 := -2*z_123*(det(M^{0,1}_{2,4}))+z_124*l2-2*z_134*det(M^{0,1}_{0,4})+2*z_234*det(M^{0,1}_{0,2});
q3 := -2*z_123*det(M^{0,1}_{2,5})+2*z_124*det(M^{0,1}_{1,5})+z_134*l3+2*z_234*det(M^{0,1}_{1,2});
q4 := -2*z_123*det(M^{0,1}_{4,5})+2*z_124*det(M^{0,1}_{3,5})-2*z_134*det(M^{0,1}_{3,4})+z_234*l4;
a := x_12*x_34-x_13*x_24+x_14*x_23;
b := x_12*y_34-x_13*y_24+x_14*y_23+x_34*y_12-x_24*y_13+x_23*y_14;
c := y_12*y_34-y_13*y_24+y_14*y_23;
u := b^2-4*a*c;
ideal(q1-z_123*t,q2-z_124*t,q3-z_134*t,q4-z_234*t,u-t^2)
)  -------deformed ideal J(t)
-----

-- Christensen, Veliche, and Weyman (Linkage classes of grade 3 perfect ideals, Thm 3.7) prove:
-- cvw: If a CM ring R of codim 3 is not Golod 
-- then either p := rank tor_1(R,k)^2 or q := rank tor_1*tor_2 is nonzero.
-- If p>0 then a general link has small betti sum. If p = 0 but q>0 then
-- the general link has the same betti sum, but also has p>0, so
-- the second general link has smaller betti sum.
-- This process leads either to a complete intersection or a Golod ring.

generalLink = J -> (
    if J == ideal(1_(ring J)) then return J;
    S:= ring J;
    J0 := gens(J)*random(S^(rank source gens J), S^(codim J));
    J' := if isHomogeneous J then (ideal(J0):(J)) else localTrim (ideal(J0):(J))
)

doubleLink = J -> generalLink generalLink J

minHomogLink = J -> (
    S := ring J;
    if J == ideal(1_S) then return J;
    genlist := J_*;
    deglist :=  unique (genlist/(g -> (degree g)_0));
    D := #deglist;
    II := apply(deglist, d -> ideal select(genlist, g -> (degree g)_0 <= d));
    codims = apply(II, I -> codim I);
    levels = apply(D, i -> gens II_i * matrix basis(deglist_i, II_i));
    regseq = levels_0 * random(source levels_0, S^{codims_0:-deglist_0});
    for i from 1 to D-1 do(
	regseq = regseq | 
	         levels_i * random(source levels_i, S^{codims_i-codims_(i-1):-deglist_i}));
    regs = ideal regseq;
    assert (isHomogeneous regs);
    assert (codim regs == codims_(D-1));
    (ideal regseq):J
    )

///
restart
load "Linkage.m2"
S = ZZ/101[x,y,z]
J = ideal"x2,xy,y3,z4"
minHomogLink J
///
    
minBetti = I -> (
    --this seems to be the fastest way to compute the (total) minimal betti numbers
    --for the local resolution, at the maximal ideal of variables, of an ideal,
    --in the inhomogeneous case.
    F = res I; -- nonminimal res
    S := ring I;
    kk := coefficientRing S;
    redd = map(kk, S, {numgens S:0});
    Fbar = redd F;
    H := prune HH Fbar;
    apply(#H, i-> rank H_i)
    )

sumBettis = J ->(
    if isHomogeneous J then (G := res trim J;
	                     sum(1+length G, i-> rank G_i))
    else
       sum minBetti J
    )

cvw = method()
cvw Ideal := Ideal => I ->(
    if I == ideal(1_(ring I)) then return I;
    I1 := I;
    s := sumBettis I1;
    J2 := generalLink (J1 := generalLink I);
    t1 := sumBettis J1;
    t2 := sumBettis J2;
    <<(s,t1,t2)<<flush<<endl;
    while s > t2 do(
      I1 = J2;
      J2 = generalLink (J1 = generalLink I1);
      s = t2;
      t1 = sumBettis J1;
      t2 = sumBettis J2;
      <<(s,t1,t2)<<flush<<endl);
      
      if t2 == 0 or J2 == ideal(1_(ring I)) then <<"CI"<<endl<<endl else
      if isGolod (ring J2/J2) then(<<"Golod"<<endl<<localTrim J2<< endl<<endl) else J2
  )

cvwh = method()
cvwh Ideal := Ideal => I ->(
    --assumes I is homogeneous, does minimal homogeneous links
    if I == ideal(1_(ring I)) then return I;    
    I1 := I;
    s := sumBettis I1;

    J2 := minHomogLink (J1 := minHomogLink I);
    t1 := sumBettis J1;
    t2 := sumBettis J2;
    <<(s,t1,t2)<<flush<<endl;
    while s > t2 do(
      I1 = J2;
      J2 = minHomogLink (J1 = minHomogLink I1);
      s = t2;
      t1 = sumBettis J1;
      t2 = sumBettis J2;
      <<(s,t1,t2)<<flush<<endl);
      
      if t2 == 0 or J2 == ideal(1_(ring I)) then <<"CI"<<endl<<endl else
      if isGolod (ring J2/J2) then(<<"Golod"<<endl<<localTrim J2<< endl<<endl) else J2
  )

--      /Applications/Macaulay2-1.16.99/share/Macaulay2/CompleteIntersectionResolutions.m2:1405:44-1426:6: --source code:

      exteriorTorModule(Matrix, ChainComplex) := (f,F) -> (
	   --Here F is a possibly nonminimal resolution of a possibly inhomogeneous module M
           --f is a matrix with entries that are homotopic to zero on F
	   --The script returns T = Tor_S(M,k) as a module over E = \wedge k**(source f):
           --In the inhomogeneous case F may not be minimal,
	   --so we cannot assume that T = k**F.
           S := ring M;
	   n := numgens S;
           k := coefficientRing S;     
	   redd := map(k,S,{n:0},DegreeMap=>d->{});	   
    	 --ring over which the Tor module will be defined
	   e := symbol e;
           E := k[e_0..e_(numcols f -1), SkewCommutative => true];
	   toE := map(E, k);

	   kF := redd F; -- this is not yet tor; we must construct the homology HH_(kF)
    	   skF := apply(3+length kF, i-> syz kF.dd_(i));
	   dbar := apply(3+length kF, i -> kF.dd_i//skF_(i-1));
	 --Now HH_i(kF) == coker dbar_(i+1) == source skF_i/image(dbar_(i+1))
    	   
	 --create the homotopies representing the action of E, first on F, then on kF  
           H := makeHomotopies1(f,F);
           goodkeys := select(keys H, k->k_1>=0);	   
	   Hk0 := hashTable apply(goodkeys, h-> (h, redd H#h));

	 --we now transfer the action of the homotopies H to the pruned homology modules:
    	 --Hk#{j,i} is to be the homotopy for the j-th generator from HH_i to HH_(i+1)
           Hk := hashTable apply(goodkeys, ke-> ke =>
	             inducedMap (coker dbar_(ke_1+2), coker dbar_(ke_1+1), 
			          map(coker dbar_(ke_1+2), source skF_(ke_1),(Hk0#ke*skF_(ke_1))//skF_(ke_1+1))
				  )
			      );

         --replace with the pruned version pHk
	   T := hashTable apply(toList(0..1+length F), i -> 
	           i => if i<= length F then prune source Hk#{0,i} else prune k^0);
	   p := apply(toList(0..1+length F), i-> (T#i.cache.pruningMap));
	   pHk := hashTable(apply(keys Hk, ke -> 
		   ke => ((p_(ke_1+1))^(-1))*Hk#ke *p_(ke_1)
	       ));
    	   
	 --now move Hk and T to E
           HkE := hashTable apply(keys pHk, ke-> ke => toE pHk#ke);
    	   TE = hashTable apply(keys T, ke -> ke => E^{-ke}**toE T#ke);

           makeModule(TE, vars E, HkE)
      )

basicKoszulSyzygies = method()
basicKoszulSyzygies Ideal := Module => I -> (
    --summodule of exteriorTorModule generated by 1; image of the Koszul complex
    --of the generators of I in the homology of the resolution of I tensored with 
    --the residue field.
S := ring I;
if I == ideal(1_S) then return"input is the unit ideal";
T := exteriorTorModule(gens I, res I);
E := ring T;
BK := prune image map(T, E^1,T_{0});
s := hf(0..numgens S, BK);
t := hf(0..numgens S, T);
<<s<<" "<<t<<" "<<sum t<<flush<<endl;
BK
)

--Long's test for Golod in monomial ideals in 3 vars; conjecture for all ideals 
--(1) [I : x1] · [I : (x2, x3)] ⊆ I for all permutations {x1, x2, x3} of {x, y, z}.
--(2) [I : x1] · [I : x2] ⊆ x3[I : (x1, x2)] + I for all permutations {x1, x2, x3} of {x, y, z}.

--this shows: no 5 generator Golod monomial ideals (any fin length golod in 3 vars that contains
--x^a,y^b also contains x^(a-1)y^(b-1), and permutations -- two more gens aren't enough.
testGolod = I -> (
    P := {{0,1,2},{1,2,0},{2,0,1}};
    G := gens ring I;    
    t1 := all(3, i-> (
	    g = G_(P_i);
    gens((I:g_0)*(I:ideal(g_1,g_2)))%I == 0
    and
    gens((I:g_0)*(I:g_1))%(g_2*(I:ideal(g_0,g_1))+I) == 0
))
)
///
S = ZZ/101[x,y,z]
I = (ideal vars S)^2
testGolod I
///

regularProducts = I -> (mm := ((S^1/M)**extend(res I, koszul gens I0, matrix{{1_S}}));
    mm_2 == 0)

localTrim = I -> (
    S := ring I;
    if not S.?maxIdeal then setMaxIdeal ideal vars S;
    ideal localMingens gens I)
end--



restart
load "Linkage.m2"
J = clkw (ZZ/32003);
R = ring J
S = ZZ/101[x,y,z]
Jbar = (map(S,R,random(S^1,S^{16:-1}))) J;
cvw Jbar
cvwh Jbar
betti res Jbar
isGolod(S/Jbar)
cvwh Jbar
J' = generalLink Jbar
minimalBetti J'
J'' = generalLink J'
minimalBetti J'' 
J''' = generalLink J''
minBetti J'''
I = monomialIdeal(x^3,x^2*y,x*y^2,y^3,x*z^2,z^3)
cvw I
CLKW 
I1 = generalLink I
I' = generalLink generalLink I
isHomogeneous I'


kk = ZZ/32003
S' = kk{x,y,z}
describe S'
J = sub(I', S')
d1 = mingens J
d2 = syz d1
d3 = syz d2
syz d3
C = complex{d1,d2,d3}
C.dd^2
prune HH C
f = d1_0_0
Jf = ideal diff(vars S', f)
f % Jf
f0 = ((gens Jf)*(f//gens Jf))_0_0
matrix{{f}} % ideal(((gens Jf)*(f//gens Jf)))
factor f0
factor f
quotientRemainder (matrix{{f}}, ((gens Jf)*(f//gens Jf)))
quotientRemainder (((gens Jf)*(f//gens Jf)), matrix{{f}})
(-15350*2629^2)_kk
T = exteriorTorModule(gens I', S^1/I');
leadTerm ann T
BK = basicKoszulSyzygies I'
G = localResolution I'
F = res I'


    


--------------
restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
M = ideal vars S
setMaxIdeal M
I0 = monomialIdeal"x3,y3,z3"
II = orbitRepresentatives(S,I0,{3,3,3})
--II/(I->annihilator exteriorTorModule I)
II/(I-> cvw I);
I = last II

I0 = II_4
--I' = doubleLink I0
I' = generalLink I0
cvw I0
betti (F = localResolution I')
om = dual F.dd_3
I'' = generalLink I'
R = S/I''
red = map(kk,R,{3:0})
omR = sub(om,R)
red gens ker omR



restart
load "Linkage.m2"
S = ZZ/32003[x,y,z]
M = ideal vars S
setMaxIdeal M

localNumGens = J -> prune (module J)/M*(module J)

d = 4 -- there are 6 golod monomial ideals with d=4, n=6. I only got through one, and partly a second.
n = 6
I0 = monomialIdeal apply(numgens S, i->S_i^d)
L = orbitRepresentatives(S, I0, n-3:d)
l = L/regularProducts
L' = L_(positions(l, t -> t))
L'_2
(L'/cvw)
cvw(L'_5)
I = L'_5
isGolod(S/I)
T = exteriorTorModule(gens I, res I)
E = ring T
ann prune((ideal vars E)*T)
I' = generalLink I
              0 1 2 3
oo34 = total: 1 6 8 3
           0: 1 . . .
           1: . . . .
           2: . 2 . .
           3: . 2 2 .
           4: . 2 4 .
           5: . . 2 3

betti res I'
T' = exteriorTorModule(gens I', res I');
E' = ring T'
ann prune((ideal vars E')*T')
--it's golod!
I'' = doubleLink I';
localPrune module I'' -- still 6 gens
elapsedTime I''' = doubleLink I''; -- 47 sec
elapsedTime localPrune module I''' -- slow!

elapsedTime res localTrim I'''
elapsedTime d1 = localMingens gens I'''; -- fast!
d2 = localsyz d1; -- slow!
F = res I''' -- fast
needsPackage "PruneComplex"
pruneComplex o24
elapsedTime H = minBetti I'''

rank H_1
#H
apply(#H, i-> H_i)

describe S
S' = kk{x,y,z}
kk = coefficientRing S'
J = sub(I''', S');
F' = res J
errorDepth = 0
redd' = map(kk, S', {numgens S':0})
Fbar' = redd F'
prune HH Fbar' -- fast!

K = ideal mingens J; -- fast!
K = ideal K_*;
res( K, Strategy => 2) -- nope
gens gb K;
gbTrace = 0
gens gb K;


I = L_6
basicKoszulSyzygies I
F = res I
F.dd_2
T = exteriorTorModule(gens I, res I);
ann oo
E = ring T
prune ((ideal vars E)*T)
ann oo
gens I




cvw L_3
S' = (ZZ/32003){x,y,z}
J' = sub(localTrim J, S');
F = res J'
F.dd_3_0_0
betti oo
L = select(orbitRepresentatives(S, I0, n-3:d)/ideal, I -> testGolod I)
L/minimalBetti
for I' in L do(
    <<sumBettis I'<<endl;
    apply(2,i-> (
	I' = doubleLink I';
	<<sumBettis I'<<flush<<endl;
	));
<<endl;
)

I = L_0
I = ideal(x^3,x^2*y,x*y^2,y^3,x^2*z,x*y*z,y^2*z,z^3)
assert(isGolod(S/I) == true)
betti res I
assert(sumBettis I == 26)
I' = generalLink I
isHomogeneous I'
betti res I'
assert(isGolod(S/I') == true)
sumBettis I' == 26
I'' = generalLink I';
isHomogeneous I'' == false

R = S/I''
K = koszul vars R
apply(4, i-> numgens prune HH_i K)
tI'' = localTrim I''
localResolution tI'' 
basicKoszulSyzygies I''

restart
load "Linkage.m2"
J = CLKW 32003
S = ring J
cvw J

minimalBetti J
S= ZZ/32003[x,y,z]
M = ideal vars S
I = (ideal vars S)^3
J = doubleLink I
trim J
J' = doubleLink J;
elapsedTime J''= doubleLink J'

elapsedTime F = res J'
kk = coefficientRing S
redd = map(kk, S, {numgens S:0})
Fbar = redd F
prune HH Fbar -- fast!

x,y,z
w
 w
  w
  
  
Tor^S(R,k) as a module over \wedge Tor_1
restart
n = 3
S = kk[x_1..x_n,y_1..y_n]


needsPackage "LocalRings"

localTrim = I -> (
    S := ring I;
    if not S.?maxIdeal then setMaxIdeal ideal vars S;
    ideal localMingens gens I)

generalLink = J -> (
    J = if class J === Ideal then J else ideal J;
    if J == ideal(1_(ring J)) then return J;
    S:= ring J;
    J0 := ideal (gens(J)*random(S^(rank source gens J), S^(codim J)));
    elapsedTime K := J0:J;
    elapsedTime J' := if isHomogeneous K then K else localTrim K
)
pregeneralLink = J -> (
    J = if class J === Ideal then J else ideal J;
    if J == ideal(1_(ring J)) then return J;
    S:= ring J;
    J0 := ideal (gens(J)*random(S^(rank source gens J), S^(codim J)));
    (J0,J)
)

S = ZZ/32003[x,y,z]
M0 = monomialIdeal(x^3,x^2*y^2,x*y^3,y^4,x^2*y*z,x*y^2*z,z^5)

end--

restart
load "mike-linkage.m2"
I = generalLink M0;
elapsedTime I = generalLink I;
elapsedTime (J0,J) = pregeneralLink ideal(I_*);
numgens J
numgens J0


elapsedTime gens gb J0;
elapsedTime gens gb ideal(J_*);
J0 = ideal J0_*;
J = ideal J_*;
elapsedTime groebnerBasis (ideal(J_*), Strategy => "F4");
elapsedTime G = groebnerBasis (ideal(J0_*), Strategy => "F4");

J0 = ideal J0_*;
J = ideal J_*;
elapsedTime groebnerBasis (ideal(J_*), Strategy => "MGB"); -- slower than F4
elapsedTime G = groebnerBasis (ideal(J0_*), Strategy => "MGB"); -- slower than F4.

numgens J0
numgens J
see J0
elapsedTime quotient(J0,J,Strategy => Iterate); -- 9 - 10 sec -- the winner! and the default.
elapsedTime quotient(J0, J_0);

m = matrix{{J_0}} | (gens J0);
elapsedTime syz(gb (m, Syzygies => true, SyzygyRows => 1, Strategy => LongPolynomial));


S' = localRing(S, ideal vars S)
elapsedTime quotient(J0,J,Strategy => Quotient); -- 15 sec

T = ZZ/32003[t,x,y,z]
J0h = ideal apply(J0_*, f-> homogenize(sub(f,T),t));
Jh = ideal apply(J_*, f-> homogenize(sub(f,T),t));
elapsedTime  J0h: Jh;
mingens oo

elapsedTime gb J0;
elapsedTime gb ideal(J_*);
for f in J_* list elapsedTime J0:f;
elapsedTime intersect oo;
for i from 0 to numgens J -1 list 
elapsedTime syz (matrix{J_*}|matrix{J0_*});
elapsedTime groebnerBasis (ideal(J_*), Strategy => "F4");
elapsedTime G = groebnerBasis (ideal(J0_*), Strategy => "F4");
m = transpose gens J | (target transpose gens J)**G;
elapsedTime syz(gb (m, Syzygies => true, SyzygyRows => 1, Strategy => LongPolynomial));
T = ZZ/32003[t, x,y,z]--, MonomialOrder => Eliminate 1]
elapsedTime groebnerBasis (t*sub(J0, T)+(1-t)*ideal(sub(J_0,T)) , Strategy => "F4")

restart
debug loadPackage("IntegralClosure", Reload=>true)
debug needsPackage "PushForward"
--errorDepth=0

-- bug 1
D=2
S = QQ[x,y,z]
R = S/ker map(QQ[t],S,{t^3,t^5,t^7})
I = ideal(y,z)
integralClosure I

D = 1
Reesi = reesAlgebra I
(fReesi,fromReesi) = flattenRing Reesi
Rbar = integralClosure fReesi
describe Rbar
RbarfReesi = map(Rbar,fReesi)
I' = ideal(select(gens fReesi, x-> first degree x === 1))
M'' = RbarfReesi I'^D/RbarfReesi I'^(D+1)
RbarR = map(Rbar,R,DegreeMap => d -> prepend(0,d))
M = pushFwd(RbarR, M'', NoPrune =>true)
extendIdeal(map(M, module I^D, M_{0..numgens I-1}))
phi = map(M, module I^D, M_{0..numgens I-1})
isWellDefined phi
I^D
ideal R
M''
(gens Rbar)/degree
M
syz dual presentation M

ideal Rbar


-- using newer integralClosure(R,A) code:
D = 1
Reesi = reesAlgebra I
Rbar = integralClosure(Reesi, R)
describe Rbar
I' = ideal(select(gens Reesi, x-> first degree x === 1))
RbarReesi = map(Rbar,Reesi)
RbarR = map(Rbar, R)
M'' = basis({D}, Rbar, SourceRing => R)
M = coimage M''
phi = map(M, module I^D, M_{0..numgens I-1})

M'' = RbarReesi I'^D/RbarReesi I'^(D+1) -- this should be basis(new grading = D), then kernel.
M = pushFwd(RbarR, M'', NoPrune =>true)
phi = map(M, module I^D, M_{0..numgens I-1})
I' = extendIdeal phi -- result.  BUG: this isn't seeming to be isom to a a map of ideals.
isWellDefined phi

RbarR = map(Rbar,R,DegreeMap => d -> prepend(0,d))
I' = ideal(select(gens fReesi, x-> first degree x === 1))
M = pushFwd(RbarR, M'', NoPrune =>true)
extendIdeal(map(M, module I^D, M_{0..numgens I-1}))
phi = map(M, module I^D, M_{0..numgens I-1})
isWellDefined phi
I^D
ideal R
M''
(gens Rbar)/degree
M
syz dual presentation M

ideal Rbar


-- take 2.  29 Dec 2020.  using newer integralClosure(R,A) code:
-- but using map from degree 0 part of Reesi...
D = 1
I = trim I
Reesi = reesAlgebra I -- this is incorrect!!  The variables are in the wrong order, if we don't do the trim above.
Rbar = integralClosure(Reesi, R)
--describe Rbar
I' = ideal(select(gens Reesi, x-> first degree x === 1))
--RbarReesi = map(Rbar,Reesi)
ringIbarAmbient = (ring I)[select(gens Rbar, x -> first degree x == 0)]
Jbar = ideal select((ideal Rbar)_*, f -> first degree f == 0)
ringIbar = ringIbarAmbient/sub(Jbar, ringIbarAmbient)  -- TODO: don't use sub...
RinR' = map(ringIbar, ring I) -- is this ok?
--describe oo
--map(Rbar, ringIbar) -- map Sbar --> Rbar.

--RbarR = map(Rbar, R)
M'' = basis({D}, Rbar, SourceRing => ringIbar)
M = coimage M''
--IinRbar = trim ideal gens gb sub(I, ringIbar)
IinRbar = RinR' I -- trim ideal gens gb sub(I, ringIbar)
phi = map(M, module IinRbar^D, M_{0..numgens I-1})
isWellDefined phi
extendIdeal phi
preimage(map(ringIbar, R), oo)
-- End of the code...

-----------------------------------
-- What about this?? I think it is not needed...
M'' = RbarReesi I'^D/RbarReesi I'^(D+1) -- this should be basis(new grading = D), then kernel.
M = pushFwd(RbarR, M'', NoPrune =>true)
phi = map(M, module I^D, M_{0..numgens I-1})
I' = extendIdeal phi -- result.  BUG: this isn't seeming to be isom to a a map of ideals.
isWellDefined phi

RbarR = map(Rbar,R,DegreeMap => d -> prepend(0,d))
I' = ideal(select(gens fReesi, x-> first degree x === 1))
M = pushFwd(RbarR, M'', NoPrune =>true)
extendIdeal(map(M, module I^D, M_{0..numgens I-1}))
phi = map(M, module I^D, M_{0..numgens I-1})
isWellDefined phi
I^D
ideal R
M''
(gens Rbar)/degree
M
syz dual presentation M

ideal Rbar
-----------------------------------

-- bug 2
R = QQ[x,y]/(x^3-y^2)
S = R[z]
--errorDepth=0
integralClosure(S, R)
integralClosure(S, S) -- this doesn't yet...
integralClosure(S, QQ)

-- Try this: if R = A[x]/I, then the integral closure should be of the form A[y]/J, or R[y]/L...
S = QQ[x,y,z]
A = S/ker map(QQ[t],S,{t^3,t^5,t^7})
I = ideal(y,z)


B = reesAlgebra I
describe B
map(B,A) -- this inclusion map is easy...
-- Now let's get integral closure of B as a graded A-algebra?
(fB,fromB) = flattenRing B
fC = integralClosure fB
see ideal groebnerBasis ideal fC
  -- generated over B by: 1, w10, w10^2
fromB
newvars = drop(gens fC, -numgens A)
newdegs = drop(degrees fC, -numgens A)
aC = A[newvars, Degrees => newdegs, Join => false]
L = trim sub(ideal fC, aC)
C = aC/L
B.icFractions = fB.icFractions
fCtoC = map(C, fC, gens(C, CoefficientRing => coefficientRing A))
B.icMap = fCtoC * fB.icMap * fromB
see C
describe C
degrees oo
-- define: generatorsInDegree(d, M), is a map f : A^N --> M, if M is a B-module, graded with respect to
--   degreesLength B - degreesLength A (i.e. of the B part of the grading)
--   and the image of f is a generating set for this A-module.
--   additionally: if M is graded in the A-part of the grading, then A^N has these degrees.
-- give the subring A of B, generatorsInDegree(d, M, CoefficientRing => A)

-- define: integral closure of B = A[x]/I, should be a ring of the form A[x,y]/L, or perhaps B[y]/L
-- perhaps: give the base ring over which it should be a flat polynomial ring?
-- integralClosure(B, CoefficientRing => A) -- default is `coefficientRing B`.

-- generators(ZZ or List, Module, CoefficientRing => A): map F --> M, F = free module over A.

-- need: a function to check homogeniety, but not all the grading vectors...
-- i.e. if B = A[x]/I, and B has one more grading that A, then is I homog wrt this grading.

------------------------------------------------------------
-- Examples ------------------------------------------------
------------------------------------------------------------
-- Example 1.
R = QQ[x,y]/(x^3-y^2)
I = ideal x
assert(integralClosure I == ideal(x,y)) -- is now failing again...
integralClosure(I,2)

-- Example 2.
R = QQ[x,y]/(x^3-y^2)
A = R[z]
A' = integralClosure A -- error: can't do frac of R[z]...

-- Example 3.
S = QQ[x,y,z]
R = S/ker map(QQ[t],S,{t^3,t^5,t^7})
I = ideal(y,z)
integralClosure I
integralClosure(I, 2)

-- Example 4.
S = QQ[x,y,z,w]
R = S/ker map(QQ[s,t],S,{t^3, s*t^5, s^3*t^7, s^4})
R' = integralClosure R -- this takes, I feel, longer than it should...
see ideal R
integralClosure I -- very time consuming...
integralClosure(I, 2)
use R'
I = ideal(y,z)
integralClosure I -- this will likely be difficult too...

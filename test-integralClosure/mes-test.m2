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

-- bug 2
R = QQ[x,y]/(x^3-y^2)
S = R[z]
errorDepth=0
integralClosure S

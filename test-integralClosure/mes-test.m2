restart
debug loadPackage("IntegralClosure", Reload=>true)
debug needsPackage "PushForward"
errorDepth=0

-- bug 1
R = QQ[x,y]/(x^3-y^2)
integralClosure ideal x
I = ideal x

R' = integralClosure R
describe R'
phi = map(R', R)
I' = phi I
integralClosure I'
needsPackage "PushForward"
pushFwd(phi, module I')
methods pushFwd
map(module I', (ring I')^1, x)
pushFwd(phi, oo)

-- I in R
R = QQ[x,y]/(x^3-y^2)
I = ideal(x)
integralClosure I

i = map(Rbar, Reesi)
(pres, m, mapf) = pushFwd i
basisOfDegreeD(LD, pres)
R' = integralClosure R
f = map(R', R)
I' = f I
I'' = integralClosure I'
M = pushFwd(f, module I'', NoPrune => true)
-- (matB,k,graphR,graphI,mat,n,varsR,mapf) = pushAuxHgs f
-- -- natural map of I --> M.
-- mapf f I_0
phi = map(M, module I, M_{0..numgens I-1})
extendIdeal phi





-- bug 2
R = QQ[x,y]/(x^3-y^2)
S = R[z]
errorDepth=0
integralClosure S

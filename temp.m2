restart
debug loadPackage "NoetherNormalForm"
debug loadPackage "PushForward"

kk = ZZ/11[]
R = ZZ/11[a,b]
R**kk
tensor(kk,R, Join=>true)
tensor(kk,R, Join=>false)
kk**R

isFiniteOverCoefficientRing (ZZ/11[x]/ideal(x^2))
isFiniteOverCoefficientRing (ZZ/11[x]/ideal(x^2-3))
isFiniteOverCoefficientRing (ZZ/11[x][y,z])
isFiniteOverCoefficientRing (ZZ/11[x][y,z]/(y^2-x,z^3-x))
isFiniteOverCoefficientRing (ZZ/11[x,t]/(x*t-1)[y,z]/(y^2-x,z^3-x))
A = ZZ/11[x,t]/(x*t-1)
R = A[y,z]/(y^2-x,z^3-x)
pushFwd map(R,A)

A = ZZ/11[x,t]/(x*t-1)
R = A[y,z]/(y^2-x,t*z^3-x)
pushFwd map(R,A)

A = ZZ/11[x]
R = A[y,z]/(y^2-x,x*z^3-x)
pushFwd map(R,A)
pushFwd map(ZZ/11,ZZ/11)

isFiniteOverCoefficientRing (ZZ[x])

isAffineRing (ZZ[x]/ideal(x^2)[y])

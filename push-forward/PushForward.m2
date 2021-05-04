newPackage(
        "PushForward",
        Version => "0.5",
        Date => "April 30, 2021",
        Authors => {{Name => "Claudiu Raicu", 
                  Email => "craicu@nd.edu", 
                  HomePage => "http://www3.nd.edu/~craicu"}},
        Headline => "push forwards of finite ring maps",
	Keywords => {"Commutative Algebra"},
        DebuggingMode => true
        )
        
--note, this version has a slight change added by Karl Schwede.  It has an option to turn off the prune calls.

export {"pushFwd", "NoPrune"}

pushFwd=method(Options => {NoPrune => false})
pushFwd(RingMap):=o->(f)->
--pfB is B^1 as an A-module
--matB is the set of monomials in B that form a set of generators as an A-module
--mapf takes as arg an element of B, and returns ??
(
     A:=source f;
     B:=target f;
     deglenA:=degreeLength A;
     deglenB:=degreeLength B;
     psh:= pushAuxHgs f;
     matB:=psh_0;
     mapfaux:=psh_1;     
     local ke;
     local freeA;

     pfB := makeModule(B^1,f,matB);
     g := map(pfB,freeA,gens pfB);
     mapf := (b) -> g*(mapfaux b); 
     pfB,matB,mapf
     )


pushFwd(RingMap,Module):=o->(f,N)->
(
     B:=target f;
     aN:=ann N;
     C:=B/aN;
     bc:=map(C,B);
     g:=bc*f;
     
     matB:=(pushAuxHgs g)_0;
     if (o.NoPrune == false) then prune makeModule(N**C,g,matB) else makeModule(N**C,g,matB)
     )

pushFwd(RingMap,ModuleMap):=o->(f,d)->
(
     A:=source f;
     B:=target f;
     pols:=f.matrix;
     pM:=source d;
     pN:=target d;
     
     amn:=intersect(ann pM,ann pN);
     C:=B/amn;
     bc:=map(C,B);
     g:=bc*f;     
     M:=pM**C;
     N:=pN**C;
   
     psh:=pushAuxHgs g;
     matB:=psh_0;
     mapf:=psh_1;     
          
     pushM:=makeModule(M,g,matB);
     pushN:=makeModule(N,g,matB);
     
     matMap:=symbol matMap;
     gR:=matB**matrix d;
     c:=numgens source gR;
     l:=numgens target gR;
     k := numcols matB;
     matMap=mutableMatrix(A,k*l,c);
     
     for i1 from 0 to c-1 do
     	  for i2 from 0 to l-1 do
	  (
       	       e:=mapf(gR_i1_i2);
	       for i3 from 0 to k-1 do matMap_(i2+l*i3,i1)=e_0_i3;	       
	   );

          if (o.NoPrune == false) then prune map(pushN,pushM,matrix matMap) else map(pushN,pushM,matrix matMap)
     )

pushFwd Ring := Sequence => opts -> (R) -> (
    -- TODO: stash the matB, pf?  Make accessor functions to go to/from gens of R over A, or M to M_A.
    pushFwd map(R, coefficientRing R)
    )

pushFwd Module := Module => opts -> (M) -> (
    -- TODO
    )

pushFwd ModuleMap := ModuleMap => opts -> (M) -> (
    -- TODO
    )

-- TODO: given: M = pushFwd N, get the maps from N --> M (i.e. stash it somewhere).
--   also, we want the map going backwards too: given an element of M, lift it to N.


-- makeModule
-- internal function which implements the push forward of a module.
-- input: 
--   N     : Module, a module over B
--   f     : RingMap, A --> B
--   matB  : matrix over B, with one row, whose entries form a basis for B over A.
--           in fact, it can be any desired subset of A-generators of B, as well.
-- output:
--   the module N as an A-module.
-- notes:
--   if A is a field, this should be easier?
--   the map mp is basically
--     A^k --> auxN (over B)
--   and its kernel are the A-relations of the elements auxN

makeModule=method()
makeModule(Module,RingMap,Matrix):=(N,f,matB)->
(
     auxN:=ambient N/image relations N;
     A:=source f;
     k:=(numgens ambient N) * (numgens source matB);
     mp:=try(map(auxN,,f,matB**gens N)) else map(auxN,A^k,f,matB**gens N);
     ke:=kernel mp;
     (super ke)/ke
     )

-- what if B is an algebra over A (i.e. A is the coefficient ring of B)
-*
    TODO.
    g = gens gb ideal L
    m = lift(matB, ring g)
    coker last coefficients(g, Monomials => m)
*-

pushAuxHgs=method()
pushAuxHgs(RingMap):=(f)-> (

    A:=source f;
    B:=target f;

    matB := null;
    mapf := null;
    
     if isInclusionOfCoefficientRing f then (
     --case when the source of f is the coefficient ring of the target:
     <<"in the coeff ring case"<<endl;	 
	 if not isFiniteOverCoefficientRing target f then error"expected a finite map";
	 matB = basis B;
         mapf = (b)->(
             (mons,cfs) := coefficients(b,Monomials=>matB);
	     lift(cfs, A)
	     );
         return(matB,mapf)
	 );

     pols:=f.matrix;
          
     FlatA:=flattenRing A;
     FA:=FlatA_0;
     iFA:=ideal FA;
     varsA:=flatten entries FlatA_1^-1 vars FA;
     RA:=try(ring source presentation FA) else FA;
     FlatB:=flattenRing B;
     FB:=FlatB_0;
     iFB:= ideal FB;
     varsB:=flatten entries FlatB_1^-1 vars FB;
     RB:=try(ring source presentation FB) else FB;
     m:=numgens FA;
     n:=numgens FB;
     
     pols=pols_{0..(m-1)};
          
     R := try(tensor(RB, RA, Join => false)) else tensor(RB, RA, Join => true);
     xvars := (gens R)_{n..n+m-1};
     yvars := (gens R)_{0..n-1};
     iA:=sub(ideal FA,matrix{xvars});
     iB:=sub(ideal FB,matrix{yvars});
     iGraph:=ideal(matrix{xvars}-sub(pols,matrix{yvars}));
     I:=iA+iB+iGraph;
     inI:=leadTerm I;
     
     r:=ideal(sub(inI,matrix{yvars | splice{m:0}}));     
     for i from 1 to n do
	if ideal(sub(gens r,matrix{{(i-1):0,1_R,(m+n-i):0}}))!=ideal(1_R) then
     	  error "map is not finite";

     mat:=lift(basis(R/(r+ideal(xvars))),R);
     k:=numgens source mat;
     matB = sub(mat,matrix{varsB|toList(m:0_B)});
     assert(k == numcols matB);
     phi:=map(R,B,matrix{yvars});
     toA:=map(A,R,flatten{n:0_A,varsA});
     mapf = (b)->(
	  (mons,cfs):=coefficients((phi b)%I,Monomials=>mat,Variables=>yvars);
	  toA cfs	  
	  );

--error "debug me";     
--     matB,k,R,I,mat,n,varsA,mapf
     matB,mapf     
     )

isInclusionOfCoefficientRing = method()
isInclusionOfCoefficientRing RingMap := Boolean => inc -> (
    --checks whether the map is the inclusion of the coefficientRing
    if source inc =!= coefficientRing target inc then return false;
    inc vars source inc == promote (vars source inc, target inc)
    )

isFiniteOverCoefficientRing = method()
isFiniteOverCoefficientRing Ring := Boolean => R -> (
    I := ideal leadTerm ideal R;
    ge := flatten select(I_*/support, ell -> #ell == 1);
    set ge === set gens ring I
    )
    
beginDocumentation()

document{
  Key => PushForward,
  Headline => "pushforward functor for finite ring maps",
  EM "PushForward", " is a package that implements the pushforward functor for finite ring maps",
  Caveat => "Works only for maps of rings finitely generated over a base field "
  }

doc ///
    Key
        (pushFwd, RingMap)
    Headline
        push forward of a finite ring map
    Usage
        pushFwd f
    Inputs
        f:RingMap
    Outputs
        :Sequence 
	 If $f: A -> B$ then the function returns
            (1) B^1 as a module over A
            (2) a 1-row matrix of elements of B whose entries generate B as A-module.
            (3) a function that
            assigns to each element B its
            representation as an element of the A-module B^1.
    Description
        Text
            Given a ring map $f : A \to B$, $B$ can be considered as a module over $A$.
            If this module is finite, this method returns this module.  And some other stuff...  Write this!
        Example
            kk = QQ;
            S = kk[a..d];
            I = monomialCurveIdeal(S, {1,3,4})
            B = S/I
            A = kk[a,d];
            f = map(R,A)
            (M,g,pf) = pushFwd f;
            M
            g
            use B
	    pf(a*b - c^2)
    Caveat
    SeeAlso
///

doc ///
    Key
        (pushFwd, RingMap, Module)
    Headline
        push forward of a module via a finite ring map
    Usage
        N = pushFwd(f, M)
    Inputs
        f:RingMap
            from a ring $A$ to a ring $R$
        M:Module
            an $R$-module, which via $f$ is a finite $A$-module
    Outputs
        N:Module
    Description
        Text
            Given a (not necessarily finite) ring map $f : A \to R$, the $R$-module $M$ can be considered as a module over $A$.
            If $M$ is finite, this method returns the corresponding $A$-module.
        Example
            kk = QQ;
            A = kk[t];
            B = kk[x,y]/(x*y);
            use B;
            i = ideal(x)
            f = map(B,A,{x})
            pushFwd(f,module i)
    Caveat
    SeeAlso
///

doc ///
    Key
        (pushFwd, RingMap, ModuleMap)
    Headline
        push forward of a module map via a finite ring map
    Usage
        gA = pushFwd(f, g)
    Inputs
        f:RingMap
            from a ring $A$ to a ring $R$
        g:ModuleMap
            (a matrix), $g : M_1 \to M_2$ of modules over $R$
    Outputs
        gA:ModuleMap
    Description
        Text
            If $M_1$ and $M_2$ are both finite generated as $A$-modules, via $f$, this returns the induced map
            on $A$-modules.
        Example
            kk = QQ
            R = kk[a,b]
            S = kk[z,t]
            f = map(S,R,{z^2,t^2})
            M = S^1/ideal(z^3,t^3)
            g = map(M,M,matrix{{z*t}})
            p = pushFwd(f,g)
            source p == pushFwd(f, source g)
            target p == pushFwd(f, target g)
            kerg = pushFwd(f,ker g)
            kerp = prune ker p
    Caveat
    SeeAlso
///

document{
  Key => pushFwd,
  Headline => "push forward",
  "The push forward functor",
  UL {
       {TO (pushFwd,RingMap)," - for a finite ring map"},
       {TO (pushFwd,RingMap,Module), " - for a module"},
       {TO (pushFwd,RingMap,ModuleMap), " - for a map of modules"}
     }
  }   

-- document{
--   Key => (pushFwd,RingMap),
--   Headline => "push forward of a finite ring map",
--   Usage => "pushFwd f",
--   Inputs => { "f" },
--   Outputs => {{"a presentation of the target of ",TT "f", " as a module over the source"},{"the matrix of generators of the target of ",TT "f"," as a module over the source"},{"a map that assigns to each element of the target of ", TT "f"," its representation as an element of the pushed forward module"}},
--   EXAMPLE lines ///
--   kk = QQ
--   S = kk[a..d]
--   I = monomialCurveIdeal(S, {1,3,4})
--   R = S/I
--   A = kk[a,d]
--   use R
--   F = map(R,A)
--   (M,g,pf) = pushFwd F;
--   M
--   g
--   pf(a*b - c^2)
--   ///,
--   Caveat => {TEX "In a previous version of this package, the third output was a function which assigned to each element of the target of ", TT "f", " its representation as an element of a free module 
--       which surjected onto the pushed forward module."}
--   }

-- document{
--   Key => (pushFwd,RingMap,Module),
--   Headline => "push forward of a module",
--   Usage => "pushFwd(f,N)",
--   Inputs => { "f", "N" },
--   Outputs => {{"a presentation of ",TT "N", " as a module over the source of ",TT "f"}},
--   TEX "Given a (not necessarily finite) ring map $f:A \\rightarrow{} B$ and a $B$-module $N$ which is finite over $A$, the function returns a presentation of $N$ as an $A$-module.",
--   PARA{},
--   EXAMPLE lines ///
--   kk = QQ
--   A = kk[t]
--   B = kk[x,y]/(x*y)
--   use B
--   i = ideal(x)
--   f = map(B,A,{x})
--   pushFwd(f,module i)
--   ///
--   }

-- document{
--   Key => (pushFwd,RingMap,ModuleMap),
--   Headline => "push forward of a map of modules",
--   Usage => "pushFwd(f,d)",
--   Inputs => { "f", "d" },
--   Outputs => {{"the push forward of the map d"}},
--   EXAMPLE lines ///
--   kk = QQ
--   R = kk[a,b]
--   S = kk[z,t]
--   f = map(S,R,{z^2,t^2})
--   M = S^1/ideal(z^3,t^3)
--   g = map(M,M,matrix{{z*t}})
--   p = pushFwd(f,g)
--   kerg = pushFwd(f,ker g)
--   kerp = prune ker p
--   ///
--   }

doc ///
Key
  NoPrune
  [pushFwd,NoPrune]
Headline
  NoPrune option for pushFwd
Description
 Text
  This is an optional argument for the @TO pushFwd@ function. Its default value is {\tt false},
  which means that the presentation of a pushed forward module is pruned by default. If NoPrune 
  is set to {\tt true}, then the prune calls in pushFwd are turned off.
 Example
  R5=QQ[a..e]
  R6=QQ[a..f]
  M=coker genericMatrix(R6,a,2,3)
  G=map(R6,R5,{a+b+c+d+e+f,b,c,d,e})
  notpruned = pushFwd(G,M,NoPrune => true)
  pruned = pushFwd(G,M)
///

--test 0
TEST ///

kk=ZZ/32003
R4=kk[a..d]
R5=kk[a..e]
R6=kk[a..f]
M=coker genericMatrix(R6,a,2,3)
pdim M

G=map(R6,R5,{a+b+c+d+e+f,b,c,d,e})
F=map(R5,R4,random(R5^1,R5^{4:-1}))

P=pushFwd(G,M)
assert (pdim P==1)

Q=pushFwd(F,P)
assert (pdim Q==0)
///

-- test 1
TEST ///
P3=QQ[a..d]
M=comodule monomialCurveIdeal(P3,{1,2,3})

P2=QQ[a,b,c]
F=map(P3,P2,random(P3^1,P3^{-1,-1,-1}))
N=pushFwd(F,M)

assert(hilbertPolynomial M==hilbertPolynomial N)
///

-- test 2
TEST ///
kk = QQ
R = kk[x,y]/(x^2-y^3-y^5)
R' = integralClosure R
pr = pushFwd map(R',R)
q = pr_0 / (pr_0)_0
use R
assert(ann q==ideal(x,y))
///

-- test 3
TEST ///
kkk=ZZ/23
kk=frac(kkk[u])
T=kk[t]
x=symbol x
PR=kk[x_0,x_1]
R=PR/kernel map(T,PR,{t^3-1,t^4-t})
PS=kk[x_0,x_1,x_2]
S=PS/kernel map(T,PS,{t^3-1,t^4-t,t^5-t^2})

rs=map(S,R,{x_0,x_1})
st=map(T,S,{t^3-1,t^4-t,t^5-t^2})

pst=pushFwd st

MT=pst_0
k=numgens MT

un=transpose matrix{{1_S,(k-1):0}}
MT2=MT**MT

mtt2=map(MT2,MT,un**id_MT-id_MT**un)
MMS=kernel mtt2

r1=trim minimalPresentation kernel pushFwd(rs,mtt2)
r2=trim minimalPresentation pushFwd(rs,MMS)
r3=trim (pushFwd rs)_0

assert(r1==r2)
assert(flatten entries relations r2 == flatten entries relations r3)
///

-- test 4
TEST ///
kk=ZZ/3
T=frac(kk[t])
A=T[x,y]/(x^2-t*y)

R=A[p]/(p^3-t^2*x^2)
S=A[q]/(t^3*(q-1)^6-t^2*x^2)
f=map(S,R,{t*(q-1)^2})
pushFwd f

p=symbol p
R=A[p_1,p_2]/(p_1^3-t*p_2^2)
S=A[q]
f=map(S,R,{t*q^2,t*q^3})
pushFwd f

i=ideal(q^2-t*x,q*x*y-t)
p=pushFwd(f,i/i^3)
assert(numgens p==2)
///

-- test 5
TEST ///
kk=QQ
A=kk[x]
B=kk[y]/(y^2)
f=map(B,A,{y})
pushFwd f
use B
d=map(B^1,B^1,matrix{{y^2}})
assert(pushFwd(f,d)==0)
///

-- test 6
TEST ///
kk=QQ
A=kk[t]
B=kk[x,y]/(x*y)
use B
i=ideal(x)
f=map(B,A,{x})
assert(isFreeModule pushFwd(f,module i))
///

-- test 7
TEST ///
kk=ZZ/101
n=3

PA=kk[x_1..x_(2*n)]
iA=ideal apply(toList(1..n),i->(x_(2*i-1)^i-x_(2*i)^(i+1)))
A=PA/iA

PB=kk[y_1..y_(2*n-1)]
l=apply(toList(1..(2*n-1)),i->(x_i+x_(i+1)))
g=map(A,PB,l)
time iB=kernel g;
B=PB/iB

f=map(A,B,l)

time h1=pushFwd g;
ph1=cokernel promote(relations h1_0,B);
time h2=pushFwd f;

assert(ph1==h2_0)
///

--test 8
TEST ///
A = QQ
B = QQ[x]/(x^2)
N = B^1 ++ (B^1/(x))
f = map(B,A)
pN = pushFwd(f,N)
assert(isFreeModule pN)
assert(numgens pN == 3) 
///

TEST///
-*
  restart
*-
  debug needsPackage "PushForward"
  kk = ZZ/101
  A = kk[s]
  B = A[t]
  C = B[u]
  f = map(C,B)
  g = map(C,B,{t})
  assert(isInclusionOfCoefficientRing f)
  assert(isInclusionOfCoefficientRing g)

  kk = ZZ/101
  A = frac (kk[s])
  B = A[t]
  C = B[u]
  f = map(C,B)
  g = map(C,B,{t})
  assert(isInclusionOfCoefficientRing f)
  assert(isInclusionOfCoefficientRing g)
///

TEST///
-*
  restart
*-
  debug  needsPackage "PushForward"
  s = symbol s; t = symbol t  
  kk = ZZ/101
  A = kk[s,t]
  -- note: this ideal is NOT the rational quartic, and in fact has an annihilator over A.
  L = A[symbol b, symbol c, Join => false]/(b*c-s*t, t*b^2-s*c^2, b^3-s*c^2, c^3 - t*b^2)
  isHomogeneous L
  describe L
  basis L
  inc = map(L, A)
  assert isInclusionOfCoefficientRing inc
  assert isFiniteOverCoefficientRing L
  (M,B,pf) = pushFwd inc -- ok.  this works, but isn't awesome, as it uses a graph ideal.
  assert( B*presentation M  == 0)
  assert(numcols B == 5)
///

TEST///
-*
  restart
*-
  debug  needsPackage "PushForward"
  s = symbol s; t = symbol t  
  kk = ZZ/101
  A = kk[s,t]
  L = A[symbol b, symbol c, Join => false]/(b*c-s*t,c^3-b*t^2,s*c^2-b^2*t,b^3-s^2*c)
  isHomogeneous L
  describe L
  basis L
  inc = map(L, A)
  assert isInclusionOfCoefficientRing inc
  assert isFiniteOverCoefficientRing L
  (M,B,pf) = pushFwd inc -- ok.  this works, but isn't awesome, as it uses a graph ideal.
  assert( B*presentation M  == 0)
  assert(numcols B == 5)
///

TEST///
-*
  restart
*-
  debug  needsPackage "PushForward"
  s = symbol s; t = symbol t  
  kk = ZZ/101
  L = kk[s, symbol b, symbol c, t]/(b*c-s*t, t*b^2-s*c^2, b^3-s*c^2, c^3 - t*b^2)
  A = kk[s,t]
  isHomogeneous L
  inc = map(L, A)
  (M,B,pf) = pushFwd inc
  assert( B * inc presentation M  == 0)
  assert(numcols B == 5)
  pushForward(inc, L^1)
///

TEST///
-*
  restart
  needsPackage "PushForward"
*-
  kk = QQ
  A = kk[x]
  R = A[y, Join=> false]/(y^7-x^3-x^2)
  pushFwd map(R,A)
  (M,B,pf) = pushFwd map(R,A)
  assert(isFreeModule M and rank M == 7)
  assert(B == basis R)
  assert( pf(y+x)- matrix {{x}, {1}, {0}, {0}, {0}, {0}, {0}} == 0)
  R' = integralClosure R
  (M,B,pf) = pushFwd map(R',R)
  use R
  assert(M == cokernel(map(R^{{0}, {-3}},R^{{-6}, {-4}},{{-x^2-x,y^4}, {y^3,-x}})))
  assert(pf w_(2,0) - matrix {{0}, {1}} == 0)
///

end--

restart
uninstallPackage"PushForward"
restart
installPackage"PushForward"
x = symbol x;y= symbol y;
check PushForward
viewHelp PushForward



target oo == pr_0
pushFwd(map(R',R), R'^1)
---
A = QQ
B = QQ[x]/(x^2)
N = B^1 ++ (B^1/(x))
f = map(B,A)
pushFwd(f,N)
pushFwd f

-- example bug -----------------------------------
-- DE + MES

///
  restart
  needsPackage "PushForward"
  

  -- This one works
  kk = ZZ/101
  A = kk[s,t]
  C = A[x,y,z]/(x^2, y^2, z^2)
  phi = map(C,A)
  f = map(C^1, A^4, phi, {{x,s*y,t*y, z}})
  ker f

  -- This one fails, degrees are screwed up.
  kk = ZZ/101
  A = kk[s,t]
  B = frac A
  C = B[x,y,z]/(x^2, y^2, z^2)
  phi = map(C,B)
  f = map(C^1, B^3, phi, {{x,s*y,z}})
  ker f
  

///

TEST ///      
-*
  restart
 
  needsPackage "NoetherNormalForm"
*-
  needsPackage "PushForward"
  s = symbol s; t = symbol t  
  kk = ZZ/101
  A = frac(kk[s,t])
  L = A[symbol a.. symbol d]/(d-t, a-s, b*c-s*t, b^2-(s/t)*c^2)
  describe L
  ML = pushFwd(map(L,frac A), L^1) -- dim 4, free -- FAILS

  -- simpler example which fails
  -- FIX THIS: should not create a graph ring.
  restart
  debug needsPackage "PushForward"
  s = symbol s; t = symbol t  
  kk = ZZ/101
  A = frac(kk[s,t])
  L = A[symbol b, symbol c]/(b*c-s*t, b^2-(s/t)*c^2)
  basis L
  describe L
  inc = map(L, A)
  assert isInclusionOfCoefficientRing inc
  assert isFiniteOverCoefficientRing L
  pushFwd inc -- fails
  --  ML = pushFwd(map(L,frac A), L^1) -- dim 4, free -- FAILS

  -- FIX THIS: should not create a graph ring.
  -- FIX ME?
  restart
  debug needsPackage "PushForward"
  s = symbol s; t = symbol t  
  A = QQ
  L = A[symbol b, symbol c]/(b*c-13, b^3-c^2)
  describe L
  inc = map(L, A)
  assert isInclusionOfCoefficientRing inc
  assert isFiniteOverCoefficientRing L
  (LA, bas, pf) = pushFwd inc -- this works
  pf(b^2+c^2) -- maybe a better way?

--non-finite example
  restart
  debug needsPackage "PushForward"
  s = symbol s; t = symbol t  
  kk = ZZ/101
  A = frac(kk[s,t])
  L = A[symbol b, symbol c]/(b^2-(s/t)*c^2 - c, c^3)
basis L
  describe L
  inc = map(L, A)
pushForward(inc, A^1)
  pushFwd inc -- fails
///

///
-- Case 1. 
-- ring map is f : A --> B = A[xs]/I, A is a polynomial ring, quotient field, basic field.

///

///
    Key
    Headline
    Usage
    Inputs
    Outputs
    Description
        Text
        Example
    Caveat
    SeeAlso
///

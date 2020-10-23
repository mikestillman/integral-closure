-*
TODO: 

Make aInfinity(Ring,ZZ) use the commutative multiplication. 
Is there an analogue for the higher products?
can we call SchurComplexes?

add the maps B -> G 

replace ** with eTensor

add associativities

construct the resolution
*-

newPackage(
	"AInfinity",
    	Version => "0.1", 
    	Date => "October 4, 2020",
        Authors => {{Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"},
	          {Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://pi.math.cornell.edu/~mike"}},
        Headline => "Compute AInfinity structures on free resolutions",
        DebuggingMode => true
    	)

export {
    "aInfinity",
    "burck",
    "golodBetti",
    --symbols
    "factors"
    }
LabeledModule = new Type of Module

labeledModule = method()
labeledModule(VisibleList,Module) := LabeledModule => (L,F) -> directSum(1:(L=>F))
--for eTensor to work, the label must be of the form {ZZ,List}, representing
--an element of G**B**B**B...
--then eTensor adds the first components, concatenates the second components.
--note that this is associative but NOT commutative.

---Code from EagonResolution.m2---------------
tensorWithComponents = method()
tensorWithComponents(Module, Module, Function) := Module => (F, G, combineIndices) -> (
    if F == 0 or G == 0 then return (ring F)^0;
    (compsF, indicesF) := componentsAndIndices F;
    (compsG, indicesG) := componentsAndIndices G;
    comps := flatten for f from 0 to #compsF-1 list (
        for g from 0 to #compsG-1 list (
            newindex := if indicesF#f === null or indicesG#g === null
	       then null else combineIndices(indicesF#f, indicesG#g);
            newindex => directSum(1:(newindex=>(compsF#f ** compsG#g)))
            )
        );
    if #comps == 0 then (ring F)^0 else directSum comps
    )

tensorWithComponents(Module, Module) := Module => (F, G) -> tensorWithComponents(F, G, (a,b) -> a|b)
tensorWithComponents(Matrix, Module, Function) := Matrix => (phi, G, combineIndices) -> (
                          src :=  tensorWithComponents(source phi, G, combineIndices);
                          tar :=  tensorWithComponents(target phi, G, combineIndices);			  
			  map(tar,src,phi**G))

eTensor = method()
eTensor(Module,Module) := Module => (F, G) -> tensorWithComponents(F, G, (a,b) ->(a#0+b#0,a#1|b#1))
eTensor(Matrix,Module) := Matrix => (phi,G) -> tensorWithComponents(phi, G, (a,b) ->(a#0+b#0,a#1|b#1))

eTensor(ChainComplex, ChainComplex) := ChainComplex => (A,B) -> ( --TODO
  C0 := A**B;
  C := chainComplex( for i from 1+min C0 to max C0 list 
	      map(directSum(for j from min A to i list A_j**B_(i-1-j)),
		  directSum(for j from min A to i list A_j**B_(i-j)),
    	          matrix(C0.dd_i)));
  C[-min C0])

eTensor(ChainComplex, ChainComplexMap) := (G,d) -> 
    map(eTensor(G,target d), eTensor (G, source d), i-> eTensor(id_(G_i), d_i))
     
	      
eTensor(Ring, List) := (R,L) -> (
    --note that A**B**C**..**D = (((A**B)**C)**..**D) = tensor(R,{A..d}).
    --The order matters for chain complexes; maybe not for modules.
    if L === {} then return R^1;
    if #L === 1 then return L_0;
    eTensor(R,drop(L,-1))**last L
    )

tensor(LabeledModule, LabeledModule) := LabeledModule => (F,G) -> (
    ans := eTensor(F,G);
    ans.cache.factors = {F,G};
    ans)
    

LabeledModule**LabeledModule := (A,B) -> tensor(A,B)

tensor(Ring, List) := o -> (R,L) -> (
    --note that A**B**C**..**D = (((A**B)**C)**..**D) = tensor(R,{A..D}).
    --The order matters for chain complexes; maybe not for modules.
    --
    if L === {} then return labeledModule{(),R^1};
    if #L === 1 then return L_0;
    ans1 := tensor(R,drop(L,-1))
    ans := ans1**last L;
    ans.cache.factors = {ans1,last L}
    )

tensorAssociativity (LabeledModule,LabeledModule,LabeledModule) := LabeledModule => (M0,M1,M1) ->(
    --produces the map from (M0**(M1**M2) to M0**M1**M2 = (M0**M1)**M2
    t := tensorAssociativity(M0,M1,M2);
    M := target source t;
    M.cache.factors = {M_0, M_1**M_2)
    directSum(1:({}=>M))
    map(M0**M1**M2, M)
    )


resassociate1 = method()
reassociate1 (LabeledModule, ZZ,ZZ) := LabeledModule => (M,ZZ,ZZ) ->(
    M0 := ((M.cache.factors)_0).cache.factors_0;
    M1 := ((M.cache.factors)_0).cache.factors_1;
    M2 := (M.cache.factors)_1;
    t := tensorAssociativity(M0,M1,M2);
    M := target t;
    M.cache.factors
///

--tensorAssociativity(1,2,3):1(23)->(12)3

assert(K**K**K**K ==((K**K)**K)**K)
--1(2(3(4))) -> 1(2,3)4 -> (1,2)3)4 = 1234
//////
--every module should have a components and a factors cache;
--only one non-empty
--the ring should have a method for transforming the label of F into F^*.
--a tensor product or direct has a list of labeled modules as its summand/factors.
--S^k has trivial label null by default;
--but user gets to label any module created


restart
loadPackage"AInfinity"

S = ZZ/101[x,y]
K = koszul matrix{{x^2,y^3}}
assert(K**K**K != K**(K**K))
assert(K**K**K == (K**K)**K)
apply(length (K**K**K), i->((K**K)**K).dd_(i+1) - (K**(K**K)).dd_(i+1))

///


TEST///
S = ZZ/101[a,b]
A = koszul vars S
B = koszul matrix{{a^2,b^3}}
C = koszul matrix{{b^4,a^5}}
assert(A**B**C == tensor(S,{A,B,C}))
assert(tensor(S,{C,B,A}) != tensor(S,{A,B,C}))
///

componentsAndIndices = (F) -> (
    if not F.cache.?components then (
        -- F has no components
        ({F}, {null})
        )
    else if #F.cache.components == 1 then (
        if F.cache.?indices then 
            ({F}, F.cache.indices)
        else 
            ({F}, {null})
        )
    else (
        a := for f in F.cache.components list componentsAndIndices f;
        (flatten(a/first), flatten(a/last))
        )
    )


golodBetti = method()
golodBetti (Module,ZZ) := BettiTally => (M,b) ->(
    --case where M is a module over a factor ring R = S/I,
    --MS is the same module over S
    --F = res I
    --K = res MS
    R := ring M;
    p := presentation R;
    S := ring p;
    phi1 := substitute(presentation M, S);
    phi := phi1 | target phi1 ** p;
    MS := prune coker phi;
    K := res MS;
    F := res coker p;
    golodBetti(F,K,b)
    )

---End of Code from EagonResolution.m2---------------


aInfinity = method()

aInfinity (Ring,ZZ) := HashTable => (R,n) -> (
    --R should be a factor ring of a polynomial ring S
    --The HashTable returned contains the A-infinity structure on an
    --S-free resolution A of R up to stage n.
    --CAVEAT: for the moment n = 3 is fixed! 

m := new MutableHashTable;

S := ring presentation R;
RS := map(R,S);


A := res coker presentation R;
B0 := chainComplex(apply(length A-1, i-> A.dd_(i+2)))[-2];
B1 := chainComplex(for i from 3 to length B0+2 list 
	map(labeledModule((,{i-1}), B0_(i-1)),
	    labeledModule((i,{}), B0_i),
	    B0.dd_i));
B := B1[-2];
m#"resolution" = B;
--m#{1,i}
apply(length B , i-> m#{1,i+3} = B.dd_(i+3));

--m#{2,i}
A0 := (chainComplex gradedModule (S^1))[-2];
d := map(A0, B, i-> if (i == 2) then A.dd_1 else 0);
m#"Bmap" = d;
N := nullhomotopy (d**id_B-id_B**d);
apply(length B, i-> m#{2,i+4} = N_(i+4));

hashTable pairs m)

    
aInfinity(HashTable, Module, ZZ) := HashTable => (mR, M,n) -> (
    --R = ring M should be a factor ring of a polynomial ring S
    --mR = aInfinity (R,n) an AInfinity structure on a resolution A of R
    --M an R-module
    --The HashTable returned contains the A-infinity structure on 
    --an S-free resolution of M up to stage n.
    --CAVEAT: for the moment n = 3, and we compute only
    --m#{i,j} for i = 1,2,3.
m := new MutableHashTable;
R := ring M;
S := ring presentation R;
RS := map(R,S);

-*
A := res coker presentation R;
B0 := chainComplex(apply(length A-1, i-> A.dd_(i+2)))[-2];
B1 := chainComplex(for i from 3 to length B0+2 list 
	map(labeledModule((,{i-1}), B0_(i-1)),
	    labeledModule((i,{}), B0_i),
	    B0.dd_i));
B := B1[-2];
*-
B := source mR#"Bmap";

G0 := res pushForward(RS,M);
G := chainComplex(for i from 1 to length G0 list 
	map(labeledModule((i-1,{}), G0_(i-1)),
	    labeledModule((i,{}), G0_(i)),
	    G0.dd_i));
m#"resolution" = G;
--m#{1,i}
  apply(length G , i-> m#{1,i+1} = G.dd_(i+1));    

--m#{2,i} 
--A0 := (chainComplex gradedModule (S^1))[-2];
--d := map(A0, B, i-> if (i == 2) then A.dd_1 else 0);
NG := nullhomotopy(G**mR#"Bmap"); --mR#"Bmap" = d
apply(length G, i-> m#{2,i+2} = NG_(i+2));

--m#{3,4}
  sour := directSum components source m#{2,3};
  m#{2,3} = map(G_2, sour, matrix m#{2,3});
  toLift :=  map(G_2, B_2**B_2**G_0, 
  - m#{2,3}*(source m#{2,3})_[0]*mR#{2,4}**id_(G_0) --*t^-1 --mR#{2,-}(mR#{2,-}**1)
  - m#{2,3}*(source m#{2,3})_[1]*(id_(B_2)**m#{2,2}) --m(1**m#{2,-})
                 );
  m#{3,4} = toLift//m#{1,3};
hashTable pairs m)

-*
burck = method()
burck(HashTable,HashTable,ZZ) := ChainComplex => (mR,mM,n) ->(
    --mR,mM are A-infinity structures on a ring R and an R-module M
    --computed at least to homological degree n.
    --construct the Golod-type resolution up to length n, using
    --Jessie Burck's recipe.
G := mM#"resolution";
B := mR#"resolution";
d := new MutableHashTable;
for i from 1 to length G do  d#(i,{0}) = G.dd_i); --mM#{1,i}
d#(0,{2})
*-

labeledProducts = method()
labeledProducts(ChainComplex, ChainComplex, ZZ) := Sequence => (A,G,n) ->(
-*    returns a pair of lists of lengths n,n+1; the first element is a list
    {A,A**A,..,(A**..**A)}; the second is a list
    {G, A**G, A**A**G..} with <= n factors, where each
    component of each product is is labeled:
    {j_1..j_s} => A_(j_1)**..**A_(j_s)  while
    (i,{j_1..j_s}) => G_i**A_(j_1)**..**A_(j_s) 
*-
    AA := apply(n, i-> eTensor(ring A, toList(i+1:A)));
    GA := apply(n+1, i-> eTensor(ring A, {G}|toList(i:A)));
    (AA,GA)
    )
    

///
restart
needsPackage "Complexes"
debug loadPackage("AInfinity",Reload => true)
S = ZZ/101[x,y,z]
R = S/(ideal gens S)^2
M = coker vars R
mR = aInfinity(R,3);
pairs mR
mM = aInfinity(mR,M,3);
pairs mM
componentsAndIndices source mR#{1,3}
componentsAndIndices target mM#{3,4}
///

beginDocumentation()

doc ///
Key
  AInfinity
Headline
  Compute the A-infinity structures on free resolutions
Description
  Text
   Following Burke's paper "Higher Homotopies and Golod Rings":
   Given an S-free resolution A -> R = S/I, set B = A_+[1] (so that B_m = A_(m-1) for m >= 2, B_i = 0 for i<2),
   and alternate differentials have changed sign.
   
   The A-infinity structure  is a sequence of degree -1 maps m_n: B^(**n) \to B such that
   m_1 is the differential, 
   mR2 is the multiplication (which is a homotopy B**B \to B lifting the degree -2 map
   d**1 - 1**d: B_2**B_2 \to B_1 (which induces 0)
       
   m_n for n>2 is a homotopy for the negative of the sum of degree -2 maps of the form
   m_(n-i+1)(1**...** 1 ** m_i ** 1 **..**),
   with inserting m_i into each possible (consecutive) sub product, and i = 2...n-1.
   Here m_1 represents the differential both of B and of B^(**n).
  Example
   I = Grassmannian(1,5, CoefficientRing => ZZ/32003); numgens(I)
   S = ring(I)
   M = S^1/I
   R = S/I
   
   A = res M; betti A
   B = (chainComplex apply(length A - 1, i -> -A.dd_(i+2)))[-2];
SeeAlso
///


TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///



end--

restart
needsPackage "Complexes"
--loadPackage("AInfinity", Reload =>true)
uninstallPackage "AInfinity"
restart
installPackage "AInfinity"



t = tensorAssociativity(B_2, B_2, B_2);
b = betti B
b ** b
(b ** b) ** b 
((b ** b) ** b ) ** b


------tensor associativity

for resolutions A of R, G of M, both length 3 , there is one nonzero component of m_3:
mM_3: B_2**B_2**G_0 ->G_3 == -mM_2(mB_2(B_2,B_2),G_0)-mM_2(B_2, mM_2(B_2,G_0))


1(2(3))->(1,2)3
1(2(3(4))) -> 1(2,3)4->(1,2)3)4
1(2(3

--why doesn't this work??

tensor List := Module => mods -> (
    if #mods == 1 then return mods_0;
    if #mods == 2 then return tensor(mods_0,mods_1);
    mods' := drop(mods,1);
    tensor(mods_0,tensor mods')
    )
mods = {S^2,S^3,S^4}
mods = {S^2,S^3}
tensor mods
tensor{S^2}

associativity = method()
associativity(List, List) := Matrix => blocks, mods -> (
-*
    blocks = {a,b,..,c} positive integers, 
    mods = {A_1,..,C_c}
    returns the map
    (A_1**..**A_a)**(B_1**..**B_b)**..**(C_1**..**C_c) -> A_1**..**C_c.
    Note that the built-in tensor product of multiple factors
    goes from left to right:
    tensorAssociativity: A*(B*C) -> A*B*C = (A*B)*C; 
*- 
    n := sum blocks;
   if blocks == {n-1,1} then tensorAssociativity(mods_0**;
   
viewHelp tensorAssociativity

S = ZZ/101[a,b,c]
G = res coker vars S
E = extend(G,schurComplex({2},G),id_(G_0))

components (source E)_2
code methods schurComplex
viewHelp SchurComplexes

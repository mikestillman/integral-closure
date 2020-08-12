newPackage(
        "ShamashResolution",
        Version => "0.9", 
        Date => "rev June 2020",
        Authors => {{Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => ""},
	      {Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"}},
        Headline => "Compute the Eagon-Shamash Resolution of the residue field",
        DebuggingMode => true
        )


export {
    "ShamashData",
    "shamashData",
    "koszulMap",

    "ShamashFreeSummand",
    "shamashFreeSummand",
    "ShamashFreeModule",
    "shamashFreeModule",
    
    "shamashFree", 
    "shamashMatrix",
    "picture",
    "shamashResolution",
    "isGolodByShamash",
    "weight",
    "HKBasis",
    "pd",
    "MaxDegree", --option for shamashFrees
    "MaxWeight", --option for shamashFrees
    
    "eagon", --a different approach
    "eBetti", -- total betti numbers from Eagon res
    "vert", --make a vertical strand of the Eagon complex
    "isIsomorphic"
    }

-- methods: dim.

-- place this into M2 core.
compositions(ZZ,ZZ,ZZ) := (nparts, k, maxelem) -> (
    -- nparts is the number of terms
    -- k is the sum of the elements
    -- each element is between 0 <= maxelem.
     compositionn := (n,k) -> (
	  if n===0 or k < 0 then {}
	  else if k===0 then {toList(n:0)}
	  else (
          set1 := apply(compositionn(n-1,k), s -> s | {0});
          set2 := apply(compositionn(n,k-1), s -> s + (toList(n-1:0) | {1}));
          set2 = select(set2, s -> s#(n-1) <= maxelem);
          join(set1, set2)
          )
      );
     compositionn = memoize compositionn;
     result := compositionn(nparts,k);
     compositionn = null;
     result
     );


ShamashData = new Type of MutableHashTable
ShamashMatrix = new Type of HashTable
ShamashFreeSummand = new Type of List --list of ZZ
ShamashFreeModule = new Type of List -- list of Shamash free summands
    --A ShamashFreeModule is represented as a list of ZZ, representing a tensor product; 
    --the first element i represents a factor K_i; subsequent elements
    --represent factors F_j. K_0 = S is suppressed (represented by the empty list).

shamashFreeModule = method()
shamashFreeModule List := ShamashFreeModule => L -> new ShamashFreeModule from L

shamashFreeSummand = method()
shamashFreeSummand List := ShamashFreeSummand => L -> new ShamashFreeSummand from L
--the first element of this list can be 0; but subsequent elements must be >=2.
--the 0th element indicates a Koszul factor K_i;
--the i-th element s_i denotes basis HH_(i-1) and has homological degree s_i.


degree ShamashFreeSummand := ZZ => L -> sum L -- homological degree
weight = method()
weight ShamashFreeSummand := ZZ => L -> if L_0 !=0 then #L else #L-1

-- plan: induction: if gamma: F_(i_1)**..**F_(i_n) is defined on such products with degree <=i and has
-- values in the sum of terms of weight (== number of factors) <=n, and the differential d is defined
-- on all terms of degree <=n, then: 
-- we define d on K_j * FF by as 
--             d(x_0**x_1**..**x_n) = d(x_0)**(x_1**..**x_n) + (-1)^(deg x_0)**x_0**d(x_1**..**x_n).
-- and we define gamma on x_1**..**x_(n+1) so that
--             d gamma(x_1**..**x_(n+1)) = - d(d(x_1**..**x_n)*x_(n+1)
-- and then 
--             d(x_1**..**x_(n+1)) = d(x_1**..**x_n)**x_n+ gamma(x_1**..**x_(n+1)).

shamashData = method()
shamashData Ring := ShamashData => (cacheValue symbol shamashData) (R -> (
    D := new ShamashData;
    D.ring = R;
    D.koszul = koszul vars R;
    i := 0;
    D#HKBasis= while (B := basis HH_i D.koszul) !=0 list (
    i = i+1;
    B); --Note that D#HKBasis_i is in homological degree i+1
    D#pd = #select(D#HKBasis, f -> f !=0) -1; 
    -- the number of nonzero Koszul groups -1. This is the projective dimension of R
    -- as module over a regular ring with the same number of variables.
    D
    ))

module(ShamashData,ShamashFreeSummand) := Module => (Data, F) ->(
    --recover the actual free module from a ShamashFreeSummand
    Fmodule := Data.koszul_(F_0);
    for i from 1 to  #F-1 do Fmodule = Fmodule**source ((Data#HKBasis)_(F_i-1));
    Fmodule
    )

module(ShamashData, ShamashFreeModule) := Module => (D,FF) ->(
    directSum(FF/(F->module(D, F)))
    )

module(Ring,ShamashFreeSummand) := Module => (R, F) -> module(shamashData R, F)
module(Ring,ShamashFreeModule) := Module => (R, FF) -> module(shamashData R, FF)

shamashFree = method(Options => {MaxDegree => InfiniteNumber, MaxWeight => InfiniteNumber})

-- warning: doesn't use the optional arguments yet.
shamashFree(ShamashData, ZZ) := ShamashFreeModule => o -> (D,n) -> (
    maxK := numgens D.ring;
    maxE := D#pd + 1;
    result := flatten for i from 0 to maxK list (
        flatten for j from 1 to (n-i)//2 list (
            c := compositions(j, n-i-2*j, maxE-2);
            for c1 in c list prepend(i, (for a in c1 list a+2))
            )
        );
    if n <= maxK then result = append(result, {n});
    shamashFreeModule (result/shamashFreeSummand)
    )

shamashFree(Ring, ZZ) := ShamashFreeModule => o -> (R,n) -> shamashFree(shamashData R, n, o)

shamashFree(ShamashData,ZZ,ZZ) := ShamashFreeModule => o -> (D,n,w) -> (
    --list of lists, representing all the ShamashFreeSummands of homological degree n 
    --and weight w that can occur.
    shamashFreeModule select(shamashFree(D,n), L -> weight L == w)
    )

shamashFree(ShamashData) := ShamashFreeModule => o -> D ->(
    --the ones of homological degree <= n and weight <= w
    )

///
restart
debug loadPackage("ShamashResolution", Reload => true)
///

TEST///
S = ZZ/101[a,b,c]
I = ideal(a,b)*ideal(a,b,c)
I = (ideal(a^2,b^3))^2
R = S/I
D = shamashData R
netList apply(5, n->shamashFree(R,n))
--netList apply(5, n->shamashFree(D,n))
time betti res (coker vars R, LengthLimit => 4)
time apply(5, n->module(R,shamashFree(R,n)))
FF = res(coker vars R, LengthLimit => 10)
assert(
    apply(length FF+1, i-> rank FF_i) == 
    apply(length FF+1, n-> rank module(R, shamashFree(R,n)))
    )

netList apply(8, n->shamashFree(R,n))
time betti res (coker vars R, LengthLimit => 8)
time apply(12, n->module(R,elapsedTime shamashFree(R,n)))
FF = res(coker vars R, LengthLimit => 15)
assert(
    apply(length FF+1, i-> rank FF_i) == 
    apply(length FF+1, n-> rank module(R, shamashFree(R,n)))
    )
///

TEST///
S = ZZ/101[a,b,c]
I = ideal(a,b)*ideal(a,b,c)
I = (ideal(a^2,b^3))^2
R = S/I
D = shamashData R
peek D
///

TEST///
S = ZZ/101[a,b,c]
I = ideal(a,b)*ideal(a,b,c)
R = S/I
D = shamashData R
assert(shamashFree(D,4,2) == shamashFreeModule ({{0, 2, 2}, {1, 3}, {2, 2}}/shamashFreeSummand))
F = shamashFreeSummand {3,1}
assert(module(R, F) == R^{-3})
///

targets = method()
targets ShamashFreeSummand := List => F -> (
    --list of lists representing all the ShamashFreeSummands of degree = deg F -1 and weight <= weight F.
    )

shamashDifferential = method()
shamashDifferential ShamashFreeSummand := F -> (
--    if weight F == 0 then 
)

gamma = method()
gamma(ShamashData, ShamashFreeSummand) := ShamashMatrix => (D,F) -> (
    )

eBetti = method()
eBetti HashTable := List => E ->(
    K := keys E;
    K00 := sort select(K, k-> k_0 == 0 and k_2 == 0);
    apply(K00, k-> rank E#k)
)

isDegreeZeroSurjection := method()
isDegreeZeroSurjection(Module,Module) := (A,B)->(
    --tests a random degree 0 map to see whether its a surjection
    H := Hom(A,B);
    B0 := basis(0,H); -- this seems to be total degree 0 in case of degreeLength>1
    f := homomorphism(B0*random(source B0, (ring B0)^1));
    coker f == 0)

isIsomorphic = method()
isIsomorphic(Module,Module) := (A,B) -> (
    --tests random degree 0 maps A->B, B->A and returns true
    --if both are surjective.
    if not(isHomogeneous A and isHomogeneous B) then 
	  error"not implemented for inhomogeneous modules";
    Ap := prune A;
    Bp := prune B;
    dA := set flatten degrees source gens Ap;
    dB := set flatten degrees source gens Bp;
    if dA =!= dB then false else    
    isDegreeZeroSurjection(Ap,Bp) and isDegreeZeroSurjection(Bp,Ap)
    )


eagon = method()
eagon(Ring, ZZ) := HashTable => (R,n) ->(
    --compute the Eagon configuration up to level n
    --Let X_i be the free module R**H_i(K), where K is the Koszul complex on the variables of R.
    --The module Y^i_j = Eagon#{0,i,j} is described in Gulliksen-Negord as:
    --Y_(i+1)^0 = Y_i^1; and 
    --for j>0, Y_(i+1)^j = Y_i^(j+1) ++ Y_i^j**X_j.

    --We count X_j as having degree j+1. With this convention, there is no component of the same degree
    --but weight exactly i+j+1 other than those in Y_i^(j+1), so, by induction,
    --Y_i^j is the sum of the components of K**(\bigotimes(\direct sum_j X_j))
    --having degree i+j and weight <= i+1. 
    
    --Each Y_i is a complex whose j-th homology is Y_i^0**X_i = H_j(Y_i^0**K) (proved in Gulliksen-Negord).

    --To construct the differential of Y_(i+1) and the map Y_(i+1) \to Y_i, this isomorphism must be made explicit.
    --Is the isomorphism given by a map of complexes from Y_i^0**K to Y_i ? Yes (trivially) for i=0.
    
    --To construct the "Eagon Resolution" to stage n is 
    --Y_n^0 \to...\to Y_2^0 \to Y_1^0 \to Y_0^0. 
    --To construct it we must construct the first n-i+1 steps of Y_i.

    D := shamashData R;
    ebasis := apply(D#HKBasis, m -> (gens target m)*matrix m); -- this makes maps ebasis_j: X_j \to K_j
    pd := length D#HKBasis - 1;
    multiplier := j -> if j<=pd then source D#HKBasis_j else R^0;
    --The maps Y_(i+1) \to Y_i will be eagon#{"W",i+1,j}
    west := "W";
    --The differential of Y_i is the sum of maps eagon#{"N",i,j} and eagon#{"NW",i,j}.
    north := "N";
    northwest :="NW";
    verticaldiff := "d";
    Eagon := new MutableHashTable;
    
    Eagon#"D" = D;
    --first make the free modules F^i_j = Eagon#{0,i,j}. 
    for i from 0 to n do(
    for j from -1 to n-i do(
      if i == 0 then Eagon#{0,i,j} = D.koszul_j else
       if j == 0 then Eagon#{0,i,j} = Eagon#{0,i-1,1}++R^0 else
        Eagon#{0,i,j} = Eagon#{0,i-1,j+1}++Eagon#{0,i-1,0}**multiplier j
    ));

    --Now make the northward maps; the maps of the complexes F^n = E#{0,i,*}
    for i from 0 to n do 
    for j from 1 to n-i do 
      if i == 0 then Eagon#{north,i,j} = D.koszul.dd_j else
        Eagon#{north,i,j} = (Eagon#{0,i,j-1})_[0]*(Eagon#{north,i-1,j+1})*(Eagon#{0,i,j})^[0]; -- map from the first component of F^i_j.

    V:= null;
    for i from 1 to n do (
    for j from  1 to n-i do 
      if i == 1 then (
         Eagon#{northwest,i,j} = if j>pd then map(Eagon#{0,i,j-1}, Eagon#{0,i,j},0) else
	       (Eagon#{0,i,j-1})_[0]*(ebasis_j)*(Eagon#{0,i,j})^[1]; -- map from the first component of F^i_j.
	 Eagon#{verticaldiff, i, j} = Eagon#{north,i,j}+Eagon#{northwest,i,j}
	 );
    Eagon
    )
)

vert = method()
vert(HashTable,ZZ) := ChainComplex => (E,i) ->(
    --the "vertical" complex F^i
    len := #select(keys E, k->k_0 === "d" and k_1 ===1);
    D:= E#"D";
    V := chainComplex apply(len-1, j-> E#{"d",i,j+1});
    X := apply(D#HKBasis, k -> source k);
    <<apply(1+length V, i-> isIsomorphic(prune HH_(i) V,  prune( X_i**HH_0 V)))<<endl;
    V
	)
///
--use mu = exteriorMultiplication n to get mu#{p,q}:wedge^pk^n ** wedge^q k^n -> wedge^(p+q) k^n,
--with bases sorted in lex. use trueKoszul vars R to get the Koszul complex with bases sorted in lex.
--these are functions in HigherCIOperators.

restart
needsPackage "DGAlgebras"
loadPackage("ShamashResolution", Reload =>true)

S = ZZ/101[a,b,c]
R = S/(ideal"ab,ac")^2 --a simple Golod ring on which to try this
E = eagon(R,5)
V=vert(E,1)
coker V.dd_1
V_0
F = res coker vars R
F.dd_2
prune (HH_0 V)

HH_2 V
ideal R
pairs E
K = keys E
isGolod R
D = shamashData R;
E#"D" = D
E#D
keys E
apply(3, i-> prune HH_i (D.koszul))
i=j=1
netList{(Eagon#{0,i,j-1})_[0], (D#HKBasis_j), (Eagon#{0,i,j})^[1]}
netList {(Eagon#{0,i,j-1})_[0],(gens target D#HKBasis_j),(D#HKBasis_j),(Eagon#{0,i,j})^[1]}
D#HKBasis
///
end-- temporary end!

beginDocumentation()

-*
restart
loadPackage "ShamashResolution"
*-

doc ///
Key
  ShamashResolution
Headline
 Construct the Shamash resolution of the residue field
Description
  Text
   Produces the components that make up a not-necessarily minimal resolution of
   the residue field of a ring R = S/I where S is a polynomial ring and I is an ideal.
   The resolution constructed is minimal if and only if R is Golod. The resolution
   constructed is called the Shamash resolution, and the description given here
   is the one from Shamash *****. 
   
   The resolution could, perhaps more properly, be called the Golod-Eagon-Shamash
   resolution. It was described, in the special case where it is minimal, by
   Golod ****. A general construction was discovered independently by Jack Eagon,
   perhaps around the same time as the paper of Shamash was written (1967),
   but not published by him. Eagon's construction, superficially different than
   the one given here, ,is described in Ch. 4 of the notes
   by Gulliksen and Levin ****.    
   
   To get a glimpse of the construction, consider the first steps. Let 
   K be the Koszul complex of S, which is the minimal S-free resolution
   of the residue field k. If numgens S = n, this begins 
   
   K_1 = S^n -> K_0 = S -> k.
   
   Let F be the mimimal S-free resolution of R.
   by the right-exactness of the tensor product, the complex
   
   R**K_1 -> R**K_0 -> k 
   
   is a presentation of k, and of course R**K_2 maps to the kernel of
   R**K_1 -> R**K_0. But there are new elements of the kernel, obtained by
   writing the generators of I, which correspond to the generators of F_1,
   in terms of the generators of the maximal ideal. Thus we must add a map
   R**F_1 -> R**K_1, and it is easy to show that the resulting complex
   
   R**F_1 ++ R**K_2 -> R**K_1 -> R**K_0 -> k
   
   is exact. There are three important points to note:
   
   1) F_0 does not occur
   
   2) F_1 occurs in homological degree 2

   3) There is a map F_1 -> K_1 that must be introduced and that does not
      come from either the complex F nor the complex K.
      
   Shamash showed that this complex can be continued to a resolution, the
   Shamash resolution. 
   The underlying graded
   module of the complex is K ** T(F'), where F' is the complex F, shifted by
   1 in homological degree so that F_i is in homological degree i+1, and truncated
   by dropping F_0; and T(F') denotes the tensor algebra on the graded module F'.

   The maps in the complex come from multiplication in the Koszul
   complex, the operation of writing a product of cycles Z_i(K)**Z_j(K) -> Z_{i+j}(K)
   as a boundary and lifting this to K_{i+j+1} (these are also the ingredients of
   the "Massey products" from topology, used by Golod to construct the complex
   in a special case,
   and the "zigzag maps" F_i -> K_i constructed from the double complex
   F**K as in the usual proof that F**k and R**K have the same homology Tor^S(R,k).
  Example
   S = ZZ/101[a,b,c]
   I = ideal(a,b,c)*ideal(b,c)
   R = S/I
   shamashResolution(5,R)
SeeAlso
 koszulMap
 shamashMatrix
 shamashFrees
///

doc ///
   Key
    shamashResolution
    (shamashResolution, ZZ, Ring)
   Headline
    computes a resolution of the residue field
   Usage
    F = shamashResolution(n,R)
   Inputs
    R:Ring
     factor ring of a polynomial ring
    n:ZZ
     number of maps to compute
   Outputs
    F:ChainComplex
     possibly non-minimal resolution of R/(ideal vars R)    
   Description
    Text
     computes the Shamash resolution
    Example
     S = ZZ/101[a,b,c]
     I = ideal(a,b,c)*ideal(b,c)
     R = S/I
     shamashResolution(5,R)
   SeeAlso
     ShamashResolution
///

doc ///
Key
 koszulMap
 (koszulMap, ZZ, ChainComplex, ChainComplex)
Headline
 Lift of the homology isomorphism minimal free resolution to Koszul complex
Usage
 fi = koszulMap(i,K,F)
Inputs
 K:ChainComplex
   Koszul Complex of the ambient polynomial ring S
 F:ChainComplex
   minimal free resolution of S/I
 i:ZZ
  index in the complex F
Outputs
 fi:Matrix
  map from F_i to K_i
Description
  Text
   Let K be the koszul complex of a polynomial ring S,
   and let F be a resolution of R := S/I. The complexes
   F ** k and R**K both compute {Tor_i}^S(R,k) = F_i**k = H_i(R**K).
   Since F_i is free, we may lift the last isomorphism to a map
   fibar: F_i -> Z_i(R**K) \subset R**K_i and then to a map
   fi: F_i -> K_i, which is computed by this function. This is the "zigzag map"
   in the double complex F**K.
  Example
   S = ZZ/101[a,b,c]
   I = ideal(a,b,c)*ideal(b,c)
   F = res I
   K = koszul vars S
   koszulMap(2,K,F)
///


doc ///
   Key
    shamashMatrix
    (shamashMatrix, List, List, ShamashData)
   Headline
    Compute the components of a map in the Shamash resolution
   Usage
    Fs = shamashMatrix(L0,L1,D)    
   Inputs
    L0 : List
     of lists, each of which specifies the components of the (i-1)st term of a Shamash resolution
    L1 : List
     of lists, each of which specifies the components of the i-th term of a Shamash resolution    
    D : ShamashData
     parts from which the Shamash resolution is built
   Outputs
    Fs : ShamashMatrix
     hashTable with keys {source,map,ring,target}
   Description
    Text
     Fs prints as a display containing the matrices that are components of the 
     i-th map in the Shamash resolution.      
    Example
     S = ZZ/101[a,b,c];
     I = ideal(a,b)*ideal(a,b,c)
     R = S/I;
     D = shamashData R
     Ls = for i from 0 to 8 list shamashFrees(D,i,2)
     Fs = for i from 1 to 8 list shamashMatrix(Ls#(i-1), Ls#i, D);
     netList for i from 0 to #Fs-2 list compose(Fs#i, Fs#(i+1))
     picture Fs#2
     matrix Fs#2
    Text
     The dots indicate that the compositions of the components are all 0, as they 
     should be in a complex.
   SeeAlso
    shamashFrees
    shamashData
    picture
    matrix
      ///
doc ///
   Key
    shamashFrees
    (shamashFrees, ZZ,ZZ,ZZ)
    (shamashFrees, ShamashData, ZZ, ZZ)
    (shamashFrees, ShamashData, ZZ, InfiniteNumber)
    (shamashFrees, ShamashData, ZZ)
   Headline
    Compute the symbols representing free modules in a term of the Shamash Resolution
   Usage
    Fr = shamashFrees(r,maxK,maxF)
    Fr = shamashFrees(D,r,maxLength)
    Fr = shamashFrees(D,r,InfiniteNumber)
    Fr = shamashFrees(D,r)    
   Inputs
    r : ZZ
     index in the resolution
    D : ShamashData
     result of shamashData I
    maxK : ZZ
     length of Koszul complex
    maxF : ZZ
     length of resolution of S/I
    maxLength : ZZ
     max of maxK, maxF (or InfiniteNumber)
   Outputs
    Fr : List
     elements are lists representing free summands of the r-th term of the Shamash Resolution
   Description
    Text
     Compute the components of a term in the Shamash Resolution.
    Example
     S = ZZ/101[a,b,c]
     I = ideal(a,b)*ideal(a,b,c)
     R = S/I
     F = res coker vars R
     D = shamashData I
     L = shamashFrees(D,3)
     sum dim(L,D) == rank F_3
   SeeAlso
    shamashData
    shamashMatrix
    dim
///

doc ///
   Key
    (dim, List, ShamashData)
   Headline
    computes the dimensions of the components of a free module
   Usage
    d = dim(L,D)
   Inputs
    L:List
     list of lists specifying summands of a free module
    D:ShamashData
     contains the Koszul complex and free resolution, from which the dimensions can be determined
   Outputs
    d:List
     of ZZ, the dimensions of the components
   Description
    Text
     L is a list of list; the element {p,q1,q2...} representing K_p**F_q1**F_q2**...
     The output is a list of the dimensions of these tensor products
    Example
     S = ZZ/101[a,b,c]
     I = ideal(a,b)*ideal(a,b,c)
     D = shamashData I
     L = shamashFrees(D,3)
     dim(L,D)
   SeeAlso
    ShamashData
    shamashData
    shamashFrees
///

doc ///
   Key
    picture
    (picture, ShamashMatrix)
   Headline
    exhibits the nonzero parts of the Shamash matrix
   Usage
    N = picture M
   Inputs
    M:ShamashMatrix
   Outputs
    N:Net
     prints a "picture" -- a net -- showing the where the nonzero blocks are
   Description
    Text
     A ShamashMatrix M is a HashTable with keys {source, map, ring, target}. Source and target are
     lists of lists representing free summands. picture M prints a net showing which source summands 
     have nonzero maps to which target summands.
    Example
     S = ZZ/101[a,b,c]
     I = ideal(a,b)*ideal(a,b,c)
     D = shamashData I
     L1 = shamashFrees(D,3)
     L0 = shamashFrees(D,2)
     M = shamashMatrix(L0, L1, D)
     picture M
     matrix M
   SeeAlso
    shamashMatrix
    shamashFrees
    shamashData
    matrix
///
 
doc ///
   Key
    (matrix, ShamashMatrix)
   Headline
    turns the HashTable respresentation into an ordinary matrix
   Usage
    M1 = matrix M
   Inputs
    M:ShamashMatrix
   Outputs
    M':Matrix
   Description
    Text
     A ShamashMatrix M is a HashTable with keys {source, map, ring, target}. Source and target are
     lists of lists representing free summands. matrix M assembles the blocks into an ordinary matrix.
    Example
     S = ZZ/101[a,b,c]
     I = ideal(a,b)*ideal(a,b,c)
     D = shamashData I
     L1 = shamashFrees(D,3)
     L0 = shamashFrees(D,2)
     M = shamashMatrix(L0, L1, D)
     picture M
     matrix M
   SeeAlso
    shamashMatrix
    shamashFrees
    shamashData
    matrix
///

doc ///
   Key
    isGolodByShamash
    (isGolodByShamash,Ring)
   Headline
    determines whether a ring is Golod
   Usage
    b = isGolodByShamash R
   Inputs
    R: Ring
     graded ring
   Outputs
    b:Boolean
     true if ring is Golod
   Description
    Text
     Tests whether shamashResolution(1+numgens R,R)
     is minimal or not. It is a result of Avramov that it
     is enough to test this much of the resolution (Reason: all the Massey operations
     are already used in the first 1+numgens R maps.)
 
     It is known (Huneke- ***) that powers of ideals are Golod
    Example
     S = ZZ/101[a,b,c]
     R = S/(ideal vars S)^2
     res(coker vars R)
     shamashResolution(4,R)
     assert(isGolodByShamash R == true)
    Text
     On the other hand, complete intersections are never Golod
    Example
     use S
     R = S/ideal"a3,b3,c3"
     res coker vars R
     F = shamashResolution(4,R)
     F.dd_4
     assert(isGolodByShamash R == false)
   SeeAlso
    shamashResolution
    ///

doc ///
   Key
    shamashData
    (shamashData, Ideal)
   Headline
    items in the construction of the Shamash resolution
   Usage
    D = shamashData I
   Inputs
    I : Ideal
     of a polynomial ring S
   Outputs
    D : ShamashData
     hashTable
   Description
    Text
     The i-th term in the Shamash resolution of the residue field over R = S/I
     is R ** a direct sum of components K_p**F_(q_1)**..**F_(q_k)
     where i = p+k = sum q_r . The maps are made from the differentials of
     K and F together with the zigzag maps f_i: F_i -> K_i constructed by 
     f_i =  koszulMap(i,K,F).
     
     The function D = shamashData I collects, in the HashTable D:
     
     I = D.Ideal
     
     R = D.ring = S/I
     
     F = D.resolution, the minimal free resolution of R
     
     F**R = D.ResolutionR
     
     K = D.koszul, the koszul complex of S
     
     K**R = D.KoszulR
     
     f_1...f_{(numgens S)} = D#"Alpha", the functions constructed by koszulMap(i,K,F).

    Example
     S = ZZ/101[a,b,c]
     I = ideal(a,b,c)*ideal(b,c)
     D = shamashData I
     keys D
     F = D.resolution
     K = D.koszul
     D#"Alpha"
   SeeAlso
    koszulMap
///

doc ///
   Key
    ShamashData
   Headline
    holds intermediate computations for shamashResolution
///


TEST ///
-*
restart
loadPackage("ShamashResolution", Reload => true)
*-
     S = ZZ/101[a,b,c]
     I = ideal(a,b,c)*ideal(b,c)
     F = shamashResolution(6,S/I)

     S = ZZ/101[a]
     I = ideal(a^3)
     F = shamashResolution(6,S/I)
--test exactness, composition 0, compare with DGAlgebras code.
-- test code and assertions here
--
-- may have as many TEST sections as needed
///

end--

restart
uninstallPackage "ShamashResolution"
restart
installPackage "ShamashResolution"
viewHelp ShamashResolution
check ShamashResolution


newPackage(
        "ShamashResolutiona",
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
    "shamashFreeModule",
    "ShamashFreeModule",
    "shamashFrees", 
    "dim",
    "shamashMatrix",
    "picture",
    "shamashResolution",
    "isGolodByShamash",
    "weight",
    "HKBasis",
    "pd",
    "MaxDegree",--option for shamashFrees
    "MaxWeight"--option for shamashFrees
    }


ShamashData = new Type of MutableHashTable
ShamashMatrix = new Type of HashTable
ShamashFreeModule = new Type of List
    --A ShamashFreeModule is represented as a list of ZZ, representing a tensor product; 
    --the first element i represents a factor K_i; subsequent elements
    --represent factors F_j. K_0 = S is suppressed (represented by the empty list).

degree ShamashFreeModule := ZZ => L -> sum L -- homological degree
weight = method()
weight ShamashFreeModule := ZZ => L -> #L
shamashFreeModule = method()
shamashFreeModule List := ShamashFreeModule => L -> new ShamashFreeModule from L

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
shamashData Ring := ShamashData => R -> (
    D := new ShamashData;
    D.ring = R;
    D.koszul = koszul vars R;
    i := 0;
    D#HKBasis= while (B := basis HH_i D.koszul) !=0 list (
    i = i+1;
    B);
    D#pd = #select(D#HKBasis, f -> f !=0) -1; 
    -- the number of nonzero Koszul groups -1. This is the projective dimension of R
    -- as module over a regular ring with the same number of variables.
    D
    )

module(ShamashData,ShamashFreeModule) := (Data, F) ->(
    --recover the actual free module from a ShamashFreeModule
    Fmodule := Data.koszul_(F_0);
    for i from 1 to weight F do Fmodule = Fmodule**source ((Data#HKBasis)_i);
    Fmodule
    )

shamashFrees = method(Options => {MaxDegree => InfiniteNumber, MaxWeight => InfiniteNumber})
shamashFrees (ShamashData, ZZ) := List => o->(D,n) -> (
    --list of shamashFreeModules: all the ShamashFreeModules of homological degree n that can occur.
    if n == 0 then return {{0}};
    P := (partitions n)/toList;
    Q := P | P/(p->{0}|p);
    Q1 := select(Q,q-> q_0<=D#pd);
    Q1/shamashFreeModule
    )

shamashFrees(ShamashData,ZZ,ZZ) := List => o-> (D,n,w) ->(
    --list of lists, representing all the ShamashFreeModules of homological degree n 
    --and weight w that can occur.
    select(shamashFrees(D,n), L -> weight L == w)
    )

shamashFrees(ShamashData) := List => o -> D ->(
    --the ones of homological degree <= n and weight <= w
    )

///
restart
loadPackage("ShamashResolutiona", Reload => true)
S = ZZ/101[a,b,c]
I = ideal(a,b)*ideal(a,b,c)
R = S/I
D = shamashData R
peek D
shamashFrees(D,0)
shamashFrees(D,4)
assert(shamashFrees(D,4,2) == {{3, 1}, {2, 2}, {0, 4}}/shamashFreeModule)
F = shamashFreeModule {3,1}
assert(module(D, F) == R^{30:-8})
///

targets = method()
targets ShamashFreeModule := List => F ->(
    --list of lists representing all the ShamashFreeModules of degree = deg F -1 and weight <= weight F.
    )

shamashDifferential = method()
shamashDifferential ShamashFreeModule := F ->(
--    if weight F == 0 then 
)

gamma = method()
gamma(ShamashData, ShamashFreeModule) := ShamashMatrix => (D,F) -> (
    )

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
     S = ZZ/101[a,b,c]
     I = ideal(a,b)*ideal(a,b,c)
     D = shamashData I
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
    dim
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
    ShamashResolution
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
debug ShamashResolution
viewHelp matrix

end--

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

-- TODO: shamashData stuff is really internal (first 4 exports). Add tests.

export {
    "ShamashData",
    "shamashData",
    "koszulMap",
    "shamashFrees", 
    "dim",
    "shamashMatrix",
    "matrixFromShamashMatrix",
    "picture",
    "shamashResolution",
    "isGolodByShamash"
    }

ShamashData = new Type of MutableHashTable
ShamashMatrix = new Type of HashTable

shamashData = method()
shamashData Ideal := ShamashData => (I) -> (
    S := ring I;
    R := S/I;
    K := koszul vars ring I; -- Koszul complex over S
    F := res I; --minimal free resolution of R over S
    D := new ShamashData;
    D.Ideal = I;
    D.ring = R;
    D.koszul = K;
    D#"KoszulR" = K ** R;
    D.resolution = F;
    D#"ResolutionR" = F ** R;
    D#"Alpha" = for i from 1 to numgens S list (koszulMap(i,K,F) ** R);
    D
    )


koszulMap = method()
koszulMap(ZZ,ChainComplex,ChainComplex) := Matrix => (i,K,F) -> (
   --Let K be the koszul complex of a polynomial ring S,
   --and let F be a resolution of R := S/I. The complexes
   --F ** k and R**K both compute Tor_*^S(R,k) = F_i**k = H_i(R**K).
   --Since F_i is free, we may lift the last isomorphism to a map
   --f'_i: F_i -> Z_i(R**K) \subset R**K_i, and then to a map 
   --f_i: F_i --> K_i, which is computed by this function.
    f := F.dd_i;
    for j from 1 to i-1 do (
        m1 := F_(i-j) ** K.dd_j;
        m2 := F.dd_(i-j) ** K_j;
        if f % m1 != 0 then << "what??";
        f = m2 * (f // m1);
        );
    f // K.dd_i
    )

free = (n, maxelem) -> (
    --lists all the terms of homological degree n that can occur.
    --each term is represented as a list of ZZ, representing a tensor product; 
    --the first element i represents a factor K_i; subsequent elements
    --represent factors F_j. K_0 = S is suppressed (represented by the empty list).
    if n == 0 then {{}} else
    flatten for i from 1 to min(maxelem, n) list (
        x := free(n-i-1,maxelem);
        x/(x1 -> prepend(i,x1))
        )
    )
shamashFrees = method()
shamashFrees(ZZ,ZZ,ZZ) := (r,maxK, maxF) -> (
    -*
     The r-th term in the Shamash resolution of the residue field over R = S/I
     is R ** a direct sum of components K_p**F_(q_1)**..**F_(q_k)
     where r = p + k + sum q_s . 
     L = shamashFrees(r,n,m) returns a list of lists of lists;
     the r-th element L_r is a list whose elements are all the lists 
     {p,q_1,..q_k} with r = p + k + sum q_s
     such that p<=maxK and q_s <= maxF.
    *-
    result := flatten for i from 0 to maxK list (
        x := free(r-i, maxF);
        x/(x1 -> prepend(i,x1))
        );
    L := result/(x -> (#x, -x#0, x))//sort/last;
    L
    )

shamashFrees(ShamashData,ZZ,InfiniteNumber) :=
shamashFrees(ShamashData,ZZ,ZZ) := (D,r,maxlength) -> (
    --applies shamashFrees with maxK and maxF taken from some shamashData.
    maxK := length D.koszul;
    maxF := length D.resolution;
    L := shamashFrees(r,maxK,maxF);
    select(L, x -> #x <= maxlength+1))

shamashFrees(ShamashData,ZZ) := (D,r) -> shamashFrees(D,r,infinity)

dim = method()
dim(List,ShamashData) := (L,D) -> (
    --L must be of the form shamashFrees(D,r)
    --returns the ranks of the components of the r-th term of the Shamash resolution.
    K := D#"KoszulR";
    F := D#"ResolutionR";
    for t in L list (
        rk := rank (K_(t#0));
        rk * product for t1 in drop(t,1) list rank (F_t1)
        )
    )
///
S = ZZ/101[a,b,c]
I = ideal(a,b)*ideal(a,b,c)
D = shamashData I
L = shamashFrees(D,3)
dim(L,D)
///

shamashMap = method()
shamashMap(List, ShamashData) := (src, D) -> (
    K := D#"KoszulR";
    F := D#"ResolutionR";
    alpha := prepend("NOT USED", D#"Alpha");

--maps {i} -> {i-1}
    if #src == 1 then (
        -- this is a Koszul map
        p := src#0;
        new HashTable from {{p-1} => K.dd_p}
        )
--maps{i,j}->{i-1,j} and {i+j}
    else if #src == 2 then (
        i := src#0;
        j := src#1;
        new HashTable from (
          if i == 0 
          then {{j} => alpha#j}
          else (
              f := wedgeProduct(i,j,K_1) * (id_(K_i) ** alpha#j);
              -- need alpha followed by multiplication
              {{i-1,j} => K.dd_i ** id_(F_j),
               {i+j} => (-1)^i * f
              }
              )
        ))
--maps f1: {i,j,k} = K_i**F_j**F_k -> K_i**K_j**F_k
    else if #src == 3 then (
        -- K_i ** F_j ** F_k
        i = src#0;
        j = src#1;
        k := src#2;
        -- first part: maps to K_i ** K_j ** F_k
-- f1,f2,f3: {0,j,k} --> {j,k} ++ {0,j+k} ++ {j+k+1}
        f1 := (-1)^(j+1) * (alpha#j ** id_(F_k));
        (f2,f3) := FKmap(j,k,D);
-- g1: {i,j,k} --> {i+j,k}
-- g2: {i,j,k} --> {i,j+k}
-- g3: {i,j,k} --> {i+j+k+1}
        if i == 0 then 
            new HashTable from {
                {i+j,k} => f1,
                {i,j+k} => f2,
                {i+j+k+1} => f3
                }
        else (
            g1 := ((wedgeProduct(i,j,K_1)) ** id_(F_k)) * (id_(K_i) ** f1);
            g2 := id_(K_i) ** f2;
            g3 := wedgeProduct(i,j+k+1,K_1) * (id_(K_i) ** f3);
            new HashTable from {
                {i-1,j,k} => K.dd_i ** id_(F_j) ** id_(F_k),
                {i+j,k} => (-1)^i * g1,
                {i,j+k} => (-1)^i * g2,
                {i+j+k+1} => (-1)^i * g3
                }
        )))

cleanShamashMap = (M) -> (
    -- a hashtable of hashtables: if any entry is the 0 matrix, that entry is removed
    M1 := for s in keys M list (
        newRow := for t in keys M#s list (if M#s#t == 0 then null else t=>M#s#t);
        s => new HashTable from delete(,newRow)
        );
    new HashTable from M1
    ) 
    
shamashMatrix = method()
shamashMatrix(List, List, ShamashData) := (tar, src, D) -> (
    F := cleanShamashMap (new HashTable from for s in src list (s => shamashMap(s,D)));
    new ShamashMatrix from {
        symbol ring => D.ring,
        symbol source => src,
        symbol target => tar,
        symbol map => F
        }
    )

///
D = shamashData I
Ls = for i from 0 to 8 list shamashFrees(D,i,2)
Fs = for i from 1 to 8 list shamashMatrix(Ls#(i-1), Ls#i, D);
netList for i from 0 to #Fs-2 list compose(Fs#i, Fs#(i+1))
///

compose(ShamashMatrix, ShamashMatrix) := (F,G) -> (
    -- F and G are hash tables of matrices, keys are descriptions of free modules
    if ring F =!= ring G then error "expected matrices with the same ring";
    M := new MutableHashTable;
    for k in G.source do (
        srcs := G.map#k;
        H := new MutableHashTable;
        for m in F.target do (
            -- add up all the products of matrices with these targets
            mats := for p in keys srcs list (h := getEntry(F,m,p,null);
                if h === null then null else h * srcs#p);
            mats = delete(null,mats);
            H#m = sum mats;
            );
        M#k = new HashTable from H;
        -- we need to take the image of each of these
        -- the way to do this: for each key in G#k, multiply it with F#(all keys)
        );
    new ShamashMatrix from {
        symbol ring => ring F,
        symbol source => G.source,
        symbol target => F.target,
        symbol map => cleanShamashMap (new HashTable from M)
        }
    )

-- Make the free modules
-- Make the matrices (as hash tables)
-- Compose the matrices

picture = method()
picture ShamashMatrix := (M) -> (
    src := M.source;
    tar := M.target;
    netList (prepend(
        prepend("", src),
        for t in tar list prepend(t, for s in src list (
                h := getEntry(M,t,s,".");
                if not instance(h, Matrix) then "" else (
                    I := ideal compress flatten h;
                    if I == 1 then "1" else "*"
                    )
                ))
        ), Alignment=>Center)
    )

getEntry = (M,t,s,val) -> if M.map#?s and M.map#s#?t then M.map#s#t else val


source ShamashMatrix := (M) -> M.source
target ShamashMatrix := (M) -> M.target
ring ShamashMatrix := (M) -> M.ring

net ShamashMatrix := (M) -> (
    src := M.source;
    tar := M.target;
    netList prepend(
        prepend("", src),
        for t in tar list prepend(t, for s in src list getEntry(M,t,s,"."))
        )
    )

matrixFromShamashMatrix = method()
matrixFromShamashMatrix ShamashMatrix := M -> (
    src := M.source;
    tar := M.target;
    mats := for t in tar list for s in src list getEntry(M,t,s,0);
    matrix mats
    )

ShamashMatrix * ShamashMatrix := (F,G) -> compose(F,G)

transpose ShamashMatrix := (M) -> (
    src := M.source;
    tar := M.target;
    newmap := new HashTable from for t in tar list (
        H := new MutableHashTable;
        for s in src do (
            x := getEntry(M,t,s,null);
            if x =!= null then H#s = transpose x;
            );
        t => new HashTable from H
        );
    new ShamashMatrix from {
        symbol ring => ring M,
        symbol source => tar,
        symbol target => src,
        symbol map => cleanShamashMap (new HashTable from newmap)
        }
    )

ShamashMatrix _ List := (M, L) -> (
    -- L should be a list of entries of M.source, this will be the submatrix of those column blocks
    newmap := for s in L list s => M.map#s;
    new ShamashMatrix from {
        symbol ring => ring M,
        symbol source => L,
        symbol target => target M,
        symbol map => cleanShamashMap (new HashTable from newmap)
        }
    )

ShamashMatrix _ Sequence := (M, entry) -> getEntry(M,entry#0,entry#1,0)

ShamashMatrix ^ List := (M,L) -> (
    newmap := for s in source M list (
        F := M.map#s;
        mats := for t in L list (if F#?t then t=>F#t else null);
        s => new HashTable from delete(null,mats)
        );
    new ShamashMatrix from {
        symbol ring => ring M,
        symbol source => source M,
        symbol target => L,
        symbol map => cleanShamashMap (new HashTable from newmap)
        }
    )

--- Creating matrices.  Here we only keep the ones we need
ShamashMapData = new Type of MutableHashTable

shamashMapData = method()
shamashMapData ShamashData := (D) -> (
    -- We create D#{i}, which is a hash table with key {i-1}
    -- D#{0,j}, with keys {j}
    -- D#{0,i,j}, with keys: {i,j}, {0,i+j}, {i+j}
    -- It does not have D#{i,j,ell}, these can be inferred
    K := D#"KoszulR";
    F := D#"ResolutionR";
    alpha := prepend("NOT USED", D#"Alpha");
    G := new ShamashMapData;
    for i from 1 to length K do addMap(G, D, {i});
    for i from 1 to length F do addMap(G, D, {0,i});
--    for i from 1 to length K do
--      G#{i} = new HashTable from {{i-1} => K.dd_i};
--    for i from 1 to length F do
--      G#{0,i} = new HashTable from {{i} => alpha#i};
    G
    )

addMap = method()
addMap(ShamashMapData, ShamashData, List) := (G, D, L) -> (
    K := D#"KoszulR";
    F := D#"ResolutionR";
    alpha := prepend("NOT USED", D#"Alpha");
    if #L == 1 then (
        i := L#0;
        if i <= 0 or i > length K then return;
        G#{i} = new HashTable from {{i-1} => K.dd_i};
        )
    else if #L == 2 then (
        i = L#0;
        j := L#1;
        if i =!= 0 then return; -- we do not need to keep that around
        if j <= 0 or j > length F then return;
        G#{0,j} = new HashTable from {{j} => alpha#j};
        )
    else if #L == 3 then (
        a := L#0;
        (i,j) = (L#1, L#2);
        if a =!= 0 then return; -- we do not need to keep that around
        if j <= 0 or j > length F then return;
        if i <= 0 or i > length F then return;
        G#{0,j} = new HashTable from {{j} => alpha#j};
        (g1,g2) := FKmap(i,j);
        G#L = new HashTable from {
            {0,i+j} => g1,
            {i+j} => g2,
            {i,j} => ((alpha D) i) ** id_(F_j)
            }
        );
    )

alpha = D -> (d) -> (
    R := D.ring;
    if instance(d,ZZ) then d = {d}
    else if instance(d, Sequence) then d = toList d;
    if #d == 1 then (
        if d#0 - 1 < #D#"Alpha" then
            D#"Alpha"#(d#0-1)
        else
            map(D#"KoszulR"_(d#0), R^0, 0)
        )
    else error "not yet defined"
    )

dkoz = D -> (i) -> D#"KoszulR".dd_i
mult = D -> (i,j) -> wedgeProduct(i,j,D#"KoszulR"_1)

liftit = (f, i, D) -> (
    -- f should be a map F --> K_i
    -- such that the image consists of cycles
    -- this returns two maps: F --> F_i, and F --> K_(i+1)
    K := D#"KoszulR";
    F := D#"ResolutionR";
    m1 := (alpha D) i;
    m2 := (dkoz D) (i+1);
    bothmodules := m1 | m2;
    g := f // bothmodules;
    g1 := g^{0..numColumns m1-1};
    g2 := g^{numColumns m1 .. numColumns bothmodules - 1};
    g1 = sub(g1, 0); -- sometimes g1 has non-zero terms in it.  There is probably a better way to insure this is a constant matrix
    f1 := (f - m1 * g1);
    if f1 % m2 != 0 then << "hmmm, maybe I have a logic error: this should have been in here\n";
    g2 = f1 // m2;
    if m1*g1 + m2*g2 != f then error "wrong";
    (g1,g2)
    --(g1,g2,m1,m2)
    )

FKmap = (i,j,D) -> (
    m := mult D;
    a := alpha D;
    f := (m(i,j)) * ((a i) ** (a j));
    liftit(f, i+j, D)
    )

shamashResolution = method()
shamashResolution (ZZ, Ring) := (n,R) ->(
    --compute first n steps of the Shamash resolution of ring I/I.
    I := ideal presentation R;
    D := shamashData I;
    frees := apply(n+1, i-> shamashFrees(D,i));
    smats := apply(n, i-> shamashMatrix(frees_i,frees_(i+1),D));
    mats := apply(n,i->matrixFromShamashMatrix smats_i);
    phi := map(R,ring mats_0 , vars R);
    chainComplex apply(n, i-> phi mats_i)
    )
///	
     S = ZZ/101[a,b,c]
     I = ideal(a,b)*ideal(a,b,c)
     R = S/I

     D = shamashData I
     L1 = shamashFrees(D,3)
     L0 = shamashFrees(D,2)
     M = shamashMatrix(L0, L1, D)
     picture M
     matrixFromShamashMatrix M
     M.source
///

isGolodByShamash = method()
isGolodByShamash Ring := R -> (
    I := ideal presentation R;
    D := shamashData I;
    n := numgens R;
    frees := apply(n+2, i-> shamashFrees(D,i));
    smats := apply(n+1, i-> shamashMatrix(frees_i,frees_(i+1),D));
    componentMats := apply(smats, M -> (
	    s := M.source;
	    flatten apply(s, ss->apply(keys M.map#ss, tt -> M.map#ss#tt))
	    ));
    p := map(R, ring((componentMats_0)_0), toList(numgens R:0_R));
    all((flatten componentMats)/(M->p M), m -> m==0)
    )

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
     matrixFromShamashMatrix Fs#2
    Text
     The dots indicate that the compositions of the components are all 0, as they 
     should be in a complex.
   SeeAlso
    shamashFrees
    shamashData
    picture
    matrixFromShamashMatrix
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
     matrixFromShamashMatrix M
   SeeAlso
    shamashMatrix
    shamashFrees
    shamashData
    matrixFromShamashMatrix
///

doc ///
   Key
    matrixFromShamashMatrix
    (matrixFromShamashMatrix, ShamashMatrix)
   Headline
    turns the HashTable respresentation into an ordinary matrix
   Usage
    M1 = matrixFromShamashMatrix M
   Inputs
    M:ShamashMatrix
   Outputs
    M':Matrix
   Description
    Text
     A ShamashMatrix M is a HashTable with keys {source, map, ring, target}. Source and target are
     lists of lists representing free summands. matrixFromShamashMatrix M assembles the blocks into an ordinary matrix.
    Example
     S = ZZ/101[a,b,c]
     I = ideal(a,b)*ideal(a,b,c)
     D = shamashData I
     L1 = shamashFrees(D,3)
     L0 = shamashFrees(D,2)
     M = shamashMatrix(L0, L1, D)
     picture M
     matrixFromShamashMatrix M
   SeeAlso
    shamashMatrix
    shamashFrees
    shamashData
    matrixFromShamashMatrix
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
viewHelp matrixFromShamashMatrix
S = ZZ/101[a..e]
I = ideal"ab-bc,b2-cd,ac-be"
I = ideal"ab,bc,cd,de,ea"
I = ideal"ab-bc,b2-cd,ac2-be2"
R = S/I

D = shamashData I
Ls = for i from 0 to 8 list shamashFrees(D,i,2)
Fs = for i from 1 to 8 list shamashMatrix(Ls#(i-1), Ls#i, D);
netList for i from 0 to #Fs-2 list compose(Fs#i, Fs#(i+1))

for m in Fs do assert isHomogeneous matrix m


L0 = shamashFrees(D,0)
L1 = shamashFrees(D,1)
L2 = shamashFrees(D,2)
L3 = shamashFrees(D,3)
L4 = shamashFrees(D,4)
L5 = shamashFrees(D,5)
L6 = shamashFrees(D,6,2)
L7 = shamashFrees(D,7,2)
L8 = shamashFrees(D,8,2)

F1 = shamashMatrix(L0, L1, D)
F2 = shamashMatrix(L1, L2, D)
F3 = shamashMatrix(L2, L3, D)
F4 = shamashMatrix(L3, L4, D);
F5 = shamashMatrix(L4, L5, D);
F6 = shamashMatrix(L5, L6, D);
F7 = shamashMatrix(L6, L7, D);
F8 = shamashMatrix(L7, L8, D);

F1*F2
F2*F3
F3*F4
F4*F5
F5*F6
F6*F7
F7*F8

M1 = matrix F1
M2 = matrix F2
M3 = matrix F3
M4 = matrix F4
M5 = matrix F5
M6 = matrix F6;
M7 = matrix F7;
M8 = matrix F8;
assert isHomogeneous M1
assert isHomogeneous M2
assert isHomogeneous M3
assert isHomogeneous M4 
assert isHomogeneous M5
assert isHomogeneous M6
assert isHomogeneous M7
assert isHomogeneous M8

ker M1 == image M2
ker M2 == image M3
ker M3 == image M4 
ker M4 == image M5
ker M5 == image M6 -- fails, since we need the map F1 ** F1 ** F1 --> ....

transpose((transpose F2) * (transpose F1))
transpose F3
F2
F2_({1},{2})
F2_{{2}}^{{1}}
F3^{{0,1}}

-- The following requires D = shamashData I, before running this code
-- alpha maps:
alpha = d -> (
    R := D.ring;
    if instance(d,ZZ) then d = {d}
    else if instance(d, Sequence) then d = toList d;
    if #d == 1 then (
        if d#0 - 1 < #D#"Alpha" then
            D#"Alpha"#(d#0-1)
        else
            map(D#"KoszulR"_(d#0), R^0, 0)
        )
    else error "not yet defined"
    )
dkoz = (i) -> D#"KoszulR".dd_i
mult = (i,j) -> wedgeProduct(i,j,D#"KoszulR"_1)
liftit = (f, i) -> (
    -- f should be a map F --> K_i
    -- such that the image consists of cycles
    -- this returns two maps: F --> F_i, and F --> K_(i+1)
    m1 := alpha i;
    m2 := dkoz (i+1);
    bothmodules := m1 | m2;
    g := f // bothmodules;
    g1 := g^{0..numColumns m1-1};
    g2 := g^{numColumns m1 .. numColumns bothmodules - 1};
    g1 = sub(g1, 0); -- sometimes g1 has non-zero terms in it.  There is probably a better way to insure this is a constant matrix
    f1 := (f - m1 * g1);
    if f1 % m2 != 0 then << "hmmm, maybe I have a logic error: this should have been in here\n";
    g2 = f1 // m2;
    if m1*g1 + m2*g2 != f then error "wrong";
    (g1,g2)
    --(g1,g2,m1,m2)
    )
FKmap = (i,j) -> (
    f := (mult(i,j)) * ((alpha i) ** (alpha j));
    liftit(f, i+j)
    )
D#"Fmap" = new MutableHashTable
D#"Kmap" = new MutableHashTable
Fpos = apply(positions(D#"Alpha", m -> m != 0), x -> x+1)
for i in Fpos do for j in Fpos do (
    (g1,g2) := FKmap(i,j);
    if g1 != 0 then D#"Fmap"#(i,j) = g1;
    if g2 != 0 then D#"Kmap"#(i,j) = g2;
    )
peek D#"Fmap"
(dkoz 2) * (mult(1,1)) * ((alpha 1) ** (alpha 1))
(dkoz 3) * (mult(2,1)) * ((alpha 2) ** (alpha 1))

FKmap(1,1)
FKmap(1,2)
FKmap(2,1)
FKmap(2,2)
FKmap(2,3)
FKmap(3,2)
FKmap(2,4)
FKmap(3,3)

D#"Fmap"#(1,2) * (id_(D#"ResolutionR"_1) ** D#"Fmap"#(1,1))
D#"Fmap"#(1,2) * (id_(D#"ResolutionR"_1) ** D#"Fmap"#(1,1))

alpha 1
alpha 2

f = (mult(1,2)) * ((alpha 1) ** (alpha 2))
(dkoz 3) * f

f = (mult(2,1)) * ((alpha 2) ** (alpha 1))
(dkoz 3) * f

liftit(
    f,
    3
    )
D#"Alpha"#0
alpha 3
alpha 2
f // (dkoz 4)
f % (dkoz 4)


n = 0.0
ntrials = 10000000
for i from 1 to ntrials do (
    x := random 1.0;
    y := random 1.0;
    if y < x^2 then n = n+1;
    )
n/ntrials

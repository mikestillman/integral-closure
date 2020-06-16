newPackage(
        "ShamashResolution",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "",
        DebuggingMode => true
        )

export {
    "ShamashData",
    "shamashData",
    "koszulMap",
    "koszulMaps",
    "shamashFrees",
    "shamashMatrix",
    "picture"
    }

ShamashData = new Type of MutableHashTable
ShamashMatrix = new Type of HashTable

shamashData = method()
shamashData Ideal := (I) -> (
    S := ring I;
    R := (ring I)/I;
    K := koszul vars ring I; -- over S
    F := res I;
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
-- Given an ideal I in a poly ring S, return the maps Fi --> Ki, where Fi = i-th term in the free res
-- and Ki = i-th term in the Koszul complex

koszulMap = method()
koszulMap(ZZ,ChainComplex,ChainComplex) := (i,K,F) -> (
    -- returns the map F_i --> K_i
    -- where 1 <= i <= n = numvars S,
    -- and S is the ring of K and F
    f := F.dd_i;
    for j from 1 to i-1 do (
        m1 := F_(i-j) ** K.dd_j;
        m2 := F.dd_(i-j) ** K_j;
        if f % m1 != 0 then << "what??";
        f = m2* (f // m1);
        );
    f // K.dd_i
    )
koszulMaps = method()
koszulMaps Ideal := (I) -> (
    F := res I;
    K := koszul vars ring I;
    (K,F)
    )

free = (n, maxelem) -> (
    if n == 0 then {{}} else
    flatten for i from 1 to min(maxelem, n) list (
        x := free(n-i-1,maxelem);
        x/(x1 -> prepend(i,x1))
        )
    )
shamashFrees = method()
shamashFrees(ZZ,ZZ,ZZ) := (r,maxK, maxF) -> (
    result := flatten for i from 0 to maxK list (
        x := free(r-i, maxF);
        x/(x1 -> prepend(i,x1))
        );
    L := result/(x -> (#x, -x#0, x))//sort/last;
    L
    )

shamashFrees(ShamashData,ZZ,InfiniteNumber) :=
shamashFrees(ShamashData,ZZ,ZZ) := (D,r,maxlength) -> (
    maxK := length D.koszul;
    maxF := length D.resolution;
    L := shamashFrees(r,maxK,maxF);
    select(L, x -> #x <= maxlength+1))
shamashFrees(ShamashData,ZZ) := (D,r) -> shamashFrees(D,r,infinity)

dim(List,ShamashData) := (L,D) -> (
    K := D#"KoszulR";
    F := D#"ResolutionR";
    for t in L list (
        rk := rank (K_(t#0));
        rk * product for t1 in drop(t,1) list rank (F_t1)
        )
    )

shamashMap = method()
shamashMap(List, List, ShamashData) := (targets, src, D) -> (
    K := D#"KoszulR";
    F := D#"ResolutionR";
    alpha := prepend("NOT USED", D#"Alpha");
    if #src == 1 then (
        -- this is a Koszul map
        p := src#0;
        new HashTable from {{p-1} => K.dd_p}
        )
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
    else if #src == 3 then (
        -- K_i ** F_j ** F_k
        i = src#0;
        j = src#1;
        k := src#2;
        -- first part: maps to K_i ** K_j ** F_k
        -*
        f1 := if i > 0 then 
            (wedgeProduct(i,j,K_1) * (id_(K_i) ** alpha#j)) ** id_(F_k)
           else (
             alpha#j ** id_(F_k)
             );
         *-
        f1 := (-1)^(j+1) * (alpha#j ** id_(F_k));
        -- now need the other two maps, to {i+j+k+1} and {i,j+k}
        (f2,f3) := FKmap(j,k,D);
-*        
        phi := (-1)^(j+1) * wedgeProduct(j,k,K_1) * (alpha#j ** alpha#k);
        if j+k < #alpha then (
            phiLifted := phi // (alpha#(j+k) | K.dd_(j+k+1));
            n1 := numgens source alpha#(j+k);
            )
        else (
            phiLifted = phi // K.dd_(j+k+1);
            n1 = 0;
            );
        n2 := numgens source K.dd_(j+k+1);
        f2 := submatrix(phiLifted, 0..n1-1,0..numgens source phiLifted-1);
        f3 := submatrix(phiLifted, n1..n1+n2-1,0..numgens source phiLifted-1);
*-        
        -- f1,f2,f3: {0,j,k} --> {j,k} ++ {0,j+k} ++ {j+k+1}
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
    F := cleanShamashMap (new HashTable from for s in src list (s => shamashMap(tar,s,D)));
    new ShamashMatrix from {
        symbol ring => D.ring,
        symbol source => src,
        symbol target => tar,
        symbol map => F
        }
    )

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

matrix ShamashMatrix := opts -> (M) -> (
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

beginDocumentation()

end--

doc ///
Key
  ShamashResolution
Headline
Description
  Text
  Example
Caveat
SeeAlso
///

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

end

restart
loadPackage "ShamashResolution"

S = ZZ/101[a..e]
I = ideal"ab-bc,b2-cd,ac-be"
I = ideal"ab,bc,cd,de,ea"
I = ideal"ab-bc,b2-cd,ac2-be2"
R = S/I

D = shamashData I
Ls = for i from 0 to 8 list shamashFrees(D,i,2)
Fs = for i from 1 to 8 list shamashMatrix(Ls#(i-1), Ls#i, D);

for i from 0 to #Fs-1 do assert(Fs#i * Fs*(i+1) == 0);
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
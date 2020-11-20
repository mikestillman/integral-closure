
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
	PackageExports => {"Complexes"},
        Headline => "Compute AInfinity structures on free resolutions",
        DebuggingMode => true
	)

export {
    "AFrees",
    "LabeledModule",
    "LabeledComplex",
    "LabeledChainComplex",
    "labeledModule",
    "getLabel",
    "labeledComplex",
    "labeledChainComplex",
    --symbols
    "label",
    "factors",
    "module",
    "symbolPairs",
--
    "aInfinity",
    "burck",
    "golodBetti",
    "labeledTensorComplex"
    }



///
uninstallPackage "AInfinity"
restart
installPackage "AInfinity"
///

///
restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R1 = S^1/(ideal vars S)^2
M = coker vars S
A = freeResolution R1
freesA = AFrees(A,5)
X = freesA#{2}++freesA#{3,2}
methods tensor

indices((components X)_1)
indices X -- just the numbers
componentsAndIndices X -- gives the labels
G = freeResolution M
G2 = G**G
componentsAndIndices (G2_1)
frees = AFrees(A,G,4)
M = frees#{3,1}
M^[{3,1}]

picture id_(frees#{3,1})
displayBlocks id_(frees#{3,1})
indices (frees#{3,1})
components frees#{3,1}
componentsAndIndices frees#{3,1}

///
labeler = (L,F) -> directSum(1:(L=>F));
///
Y = labeler({1},S^1)
Z = labeler({2},S^1)
X = Y++Z
components X
indices X -- gives the numbers
indices\components X
componentsAndIndices X -- correct.

///

AFrees = method()
AFrees(Complex, ZZ) := HashTable => (Rres, bound) ->(
    -- A is a resolution of a ring R = S/I (as S-module S^1/I)
    -- returns a hash table of the labeled tensor products of free S-modules
    -- needed for forming the A-infinity structure on the resolution A
S := ring Rres;
B := (complex apply(length Rres - 1, i -> -Rres.dd_(i+2)))[-2];
frees := new MutableHashTable;
for n from 0 to bound do (
    bS := bSymbols(length Rres, n);
    apply(bS, s -> (
      frees#s = labeler(s,tensor(S,apply(#s, t->B_(s_t))))
	    )));
    hashTable pairs frees)

AFrees(Complex, Complex, ZZ) := HashTable => (Rres,Mres,bound) ->(
    -- A is a resolution of a ring R = S/I (as S-module S^1/I)
    -- G is a resolution of an R-module M (as S-module)
    -- returns a hash table of the labeled tensor products of free S-modules
    -- needed for forming the A-infinity structure on the two resolutions.
S := ring Rres;
B := (complex apply(length Rres - 1, i -> -Rres.dd_(i+2)))[-2];
frees := new MutableHashTable;
for n from 0 to bound do (
    bS := bSymbols(length Rres,length Mres, n);
    apply(bS, s -> (
      frees#s = labeler(s,tensor(S,apply(#s, t->(
			if t<#s-1 then B_(s_t) else Mres_(s_t)))));
	    )));
    hashTable pairs frees)

bSymbols = method()
bSymbols(ZZ,ZZ) := List => (pdR,d) ->(
--    lists of non-negative integers s_0..s_k that sum to d
--    such that 2 <= s_i <= maxA for all i
    lb := for k from 1 to d//2 list toList(k:2);
    C := for k from 1 to d//2 list compositions(k, d-2*k);
    B' := flatten apply(d//2, i -> C_i/(L-> L+lb_i));
    select(B', s -> all(#s, i-> s_i <= pdR+1))
    )

bSymbols(ZZ,ZZ,ZZ) := List => (pdR,pdM,d) ->(
--    lists of non-negative integers s_0..s_k that sum to d
--    such that 2 <= s_i <= maxA for i<k and 0<=s_k<=maxG.
    lb := apply(1+d//2, i-> toList(i:2)|{0});
    C := for k from 1 to d//2 + 1 list compositions(k, d-2*(k-1));
    B' := flatten apply(d//2+1, i -> C_i/(L-> L+lb_i));
    select(B', s -> all(#s-1, i-> s_i <= pdR+1) and s_(#s-1) <= pdM)
    )

targets1 = method()
targets1 (VisibleList, ZZ) := List => (s,j) -> (
    --s is a bSymbol, j>=1.
    --output is a list of targets of maps collapsing j indices in the A-infinity structure on Rres
    len := #s;
    if j > len then return {} else
    if j == 1 then (
	L' := apply(len, i->apply(#s, k-> if k == i then s_k-1 else s_k));
    L := select(L', t -> all(len, i -> t_i >= 2));
	  ) else
    L = for i from 0 to len-j list 
      s_(toList(0..i-1))|{-1+sum(j, k -> s_(i+k))}|s_(toList(i+j..len-1));
    L
	 )

targets = method()
targets (VisibleList, ZZ) := List => (s,j) -> (
    --s is a bSymbol, j>=1.
    --output is a list of targets of maps collapsing j indices in the A-infinity structure on Rres**Mres
    len := #s;
    if j > len then return {} else
    if j == 1 then (
	L' := apply(len, i->apply(#s, k-> if k == i then s_k-1 else s_k));
    L := select(L', t -> all(len - 1, i -> t_i >= 2) and last t >= 0)
	  ) else
    L = for i from 0 to len-j list 
      s_(toList(0..i-1))|{-1+sum(j, k -> s_(i+k))}|s_(toList(i+j..len-1));
    L
	 )

maps = method()
maps(Complex, ZZ) := HashTable => (Rres, bound) ->(
    --inductively construct the maps m_j on tensor products of degree d
    S := ring Rres;
    pdR := length Rres; 
    B := (complex apply(length Rres - 1, i -> -Rres.dd_(i+2)))[-2];

    frees := AFrees(Rres,bound);
    symbols := keys frees;
    m := new MutableHashTable;
    
    for d from 1 to bound do(
	for j from 1 to d do(
           ss := select(symbols, s -> sum s == d and length s == j); 
	    for s in ss do(
		for t in targets1(s,j) do
	        if j == 1 then (
		   if s_0 == 2 then m#(j,s) = 0 else  
		                    m#(j,s) = map(frees#t,frees#s, B.dd_(s_0)));
		if j == 2 then (
                    A0 := (complex S^1)[-2];
		    d1 := map(A0,B, i -> if (i == 2) then Rres.dd_1 else 0);
		    m2 := nullHomotopy (d1 ** id_B - id_B ** d1);
		    indices(source m2_5);
		    error();
		    	    ))));
    hashTable pairs m)
--	<<(d,j)<<ss<<endl;

suitable = method()
suitable List := v-> 
     -- v is a list of ZZ. returns null unless v has the form
     -- {0...0,1,0..0}, in which case it returns the position of the 1.
                  if min v == 0 then position (v, vv -> vv == 1) else null;
tensorList = method()
tensorList List := Module => L -> (
    --tensor product of a list of modules
    if not class L_0 =!= Module then error "Input should be a list of Modules.";
    S := ring L_0;
    if #L == 0 then return S^1;
    if #L == 1 then return L_0;
    if #L > 1  then return tensorList(drop(L, -1)) ** last L)
    
		  
labeledTensorComplex = method()
labeledTensorComplex List := Complex => L -> (
    --L = {C_0..C_(p-1)}, list chain complexes. Form the tensor product of the C_i
    --in such a way that if the tensor products of the modules (C_i)_m are labeled,
    --then the modules of the tensor product are direct sums of modules from the hashtable, so that
    --componentsAndIndices applied to pC gives the correct list of indices, and
    --thus picture pC.dd_m works.
    if class L_0 =!= Complex then error"Input should be a list of Complexes.";
    S := ring L_0;
    if #L == 1 and class L_0 === Complex then (
	B := L_0;
	F := for i from min B to max B list labeler({i}, B_i);
	B' := complex for i from min B to max B -1 list map(F_(i-min B),F_(i+1-min B), B.dd_(i+1));
	return B'[-min B]
        );
    p := #L;
    Min := apply(L, C->min C);
    Max := apply(L, C->max C-1);
    modules := apply(#L + sum Max - sum Min, i ->(
	    d := i+sum Min;
	    com := select(compositions(p,d), c -> all(p, i->Min_i <= c_i and c_i<= Max_i) and c != {});
	    apply(com, co -> (co => labeler(co, tensor(S,apply(p, pp->(L_pp)_(co_pp))))))
	));
    modules = select(modules, tt-> #tt != 0);

    d := for i from 0 to #modules -2 list(	
        map(directSum modules#i,
            directSum modules#(i+1),
            matrix table( -- form a block matrix
                modules#i, -- rows of the table
                modules#(i+1), -- cols of the table
                (j,k) -> ( -- j,k each have the form (List => Module)
		    indtar := j#0;
		    indsrc := k#0;		    
                    tar := j#1;
                    src := k#1;
		    p := suitable(indsrc - indtar);
                    m := map(tar, src, 
			if p === null then 0 else(
			sign := (-1)^(sum(indsrc_(toList(0..p-1))));
			phi := sign*(tensor(S, apply(p, q -> L_q_(indtar_q)))**
			                                (L_p).dd_(indsrc_p)**
                               tensor(S, apply(#L-p-1, q -> L_(p+q+1)_(indtar_(p+q+1)))))
			))))));
                   (complex d)[-sum(L, ell -> min ell)])
labeledTensorComplex Complex := Complex => C -> labeledTensorComplex{C}
lTC = labeledTensorComplex;

///
restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R1 = S^1/ideal(a,b)
A = (freeResolution R1) [-3]
A' = lTC {A}
picture(A'.dd_5)
T = lTC{A,A,A}
(T.dd^2)
indices T_10
componentsAndIndices T_27
picture T.dd_10
picture A'.dd_1
///

///
restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c,d]
R = S/(ideal(a,b,c,d))^2
elapsedTime H = aInfinity(R,3); -- potentionall slower than with chainComplexes.
K = toSequence (keys H)_{2..#keys H -1}
K = select(K, k-> class k === List)
for k in K do <<k<<" "<< picture H#k<<endl;

///

aInfinity = method()
aInfinity (Ring,ZZ) := HashTable => (R,n) -> (
    --R should be a factor ring of a polynomial ring S
    --The HashTable returned contains the A-infinity structure on an
    --S-free resolution A of R up to m_n: B^(**n) --> B
    --CAVEAT: for the moment n = 3 is fixed! 

m := new MutableHashTable;

S := ring presentation R;
RS := map(R,S);
A' := freeResolution coker presentation R;
A'' := labeledTensorComplex(A'[-1]);
A := A''[1];
B0 := complex(apply(length A-1, i-> A.dd_(i+2)))[-2];
B1 := complex(for i from 3 to length B0+2 list 
	map(B0_(i-1),
	    B0_i,
	    B0.dd_i));
--B := labeledTensorComplex{B1[-2]};
B := B1[-2];
m#"resolution" = B;
--m#{1,i}
apply(length B , i-> m#{1,{i+3}} = B.dd_(i+3));

--m#{2,i}
A0 := (complex S^1)[-2];
d := map(A0, B, i-> if (i == 2) then A.dd_1 else 0);
m#"Bmap" = d;
B2 := labeledTensorComplex{B,B};
elapsedTime N := nullHomotopy (d**id_B-id_B**d);
for i from 2*min B to max B+1 do (
	(C,K) := componentsAndIndices (B2_i); 
	for j from 0 to #K -1 do 
	  if target N_i !=0 then
	     m#{2,K_j} = map(B_(sum K_j - 1),C_j, N_(i)*((B2_i)_[K_j]))
	                       );
B3 := labeledTensorComplex toList(3:B);
e := apply(3, ell -> toList(ell:0)|{1}|toList(3-ell-1:0));

for i from 3*2 to max B+1 do(
        co := select(compositions(3,i,max B), c -> min c >= min B);
	--(C,K) := componentsAndIndices (B2_i); is this better?
	for k in co do(
	dm3 := m#{2,{sum k_{0,1}-1,k_2}} * (m#{2,k_{0,1}}**B_(k_2)) +
	
	       -1^(k_0)* m#{2,{2,sum k_{1,2}-1}} * (B_(k_0)**m#{2,k_{1,2}}) +
        
	       sum(apply(3, ell -> if min(k-e_ell)< min B then 0 else 
		       -1^(sum k_{0..ell-1})*m#{3,k-e_ell}*m#{1,k}));
	       
	m3 := dm3//B.dd_(i-1);
        m#{3,k} = map(B_(i-1), B3_i, m3))
     );
hashTable pairs  m
)
///
restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[x_1..x_4]
R = S/(ideal vars S)^2
A = freeResolution coker presentation R
elapsedTime lTC{A,A,A}
elapsedTime A**A**A
needsPackage "Complexes"
A' = complex A

elapsedTime A'**(A'**A')
elapsedTime o10**o10

H = aInfinity(R,3);
K = sort select(keys H, k->class k === List)
for k in K do <<k<<" "<< picture(H#k)<< betti H#k <<endl;
H#{2,{2,4}}

restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[x_1..x_4]
R = S/(ideal vars S)^2
H = aInfinity(R,3);
K = sort select(keys H, k->class k === List)
for k in K do <<k<<" "<< picture(H#k)<< betti H#k <<endl;
H#{2,{2,4}}

restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R = S/ideal"a2-bc,b2,c2,ab,ac"
H = aInfinity(R,3);
K = sort select(keys H, k->class k === List)
for k in K do <<k<<" "<< picture(H#k)<< betti H#k <<endl;
H#{2,{2,3}}
H#{2,{3,2}}

///

    
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
MS := pushForward(RS,M);
B := m#resolution; -- this is truncated, labeled.

G0 := freeResolution pushForward(RS,M);
G := complex(for i from 1 to length G0 list 
	map(labeledModule((i-1,{}), G0_(i-1)),
	    labeledModule((i,{}), G0_(i)),
	    G0.dd_i));
m#"resolution" = G;
--m#{1,i}
  apply(length G , i-> m#{1,i+1} = G.dd_(i+1));    

--m#{2,i} 
BG := labeledTensorComplex{B,G};
d0 := dual syz B.dd_3;
m20 := map(S^1**G_0, B_2**G_0, d0**G_0)//G.dd_1; 
G := complex G;
BG := complex BG;
G' := naiveTruncation(G,1,infinity);
m2 := extend(G',BG,m20,-1);
)
-*
--m#{3,4}
  sour := directSum components source m#{2,3};
  m#{2,3} = map(G_2, sour, matrix m#{2,3});
  toLift :=  map(G_2, B_2**B_2**G_0, 
  - m#{2,3}*(source m#{2,3})_[0]*mR#{2,4}**id_(G_0) --*t^-1 --mR#{2,-}(mR#{2,-}**1)
  - m#{2,3}*(source m#{2,3})_[1]*(id_(B_2)**m#{2,2}) --m(1**m#{2,-})
                 );
  m#{3,4} = toLift//m#{1,3};
hashTable pairs m)
*-


///
installPackage "Complexes"
help naiveTruncation
s = {4,3,2,1}
targets(s,1)
targets(s,2)
targets(s,3)
targets(s,4)
targets(s,5)
///


symbolPairs = method()
symbolPairs (ZZ,ZZ,ZZ,ZZ) := List => (pdR, pdM, n, j) -> (
    --list of lists {p,q,s,t} such that s = (u,i), t = (v,j) are symbols; degree s = n, degree t = n-1; 
    --and s,t are equal in the places <p and >q, and q-p+1 = j.
    for s in bSymbols(pdR, pdM, n) list targets(s,j)/(t -> {s,t}))

///
bSymbols(3,3,7)
targets({2,4,0},2)
targets({2,0},2)
symbolPairs(3,3,5,2)
///

picture = method()
picture Matrix := (M1) -> (
    M := flattenBlocks M1;
    src := indices source M;
    tar := indices target M;
--    src := labels source M;
--    tar := labels target M;
    netList (prepend(
        prepend("", src),
        for t in tar list prepend(t, for s in src list (
                mts := M^[t]_[s];
		cont := ideal M^[t]_[s];
                h := if mts == 0 then "." else if (numrows mts == numcols mts and mts == 1) then "id" else 
		if cont == ideal(1_(ring mts)) then "u" else "*"
                ))
        ), Alignment=>Center)
    )

flattenBlocks = method()
flattenBlocks Module := (F) -> (
    if not isFreeModule F then error "expected a free module";
    (comps, inds) := componentsAndIndices F;
    compsLabelled := for i from 0 to #comps-1 list (
-*        if inds#i === null then (
            if rank comps#i > 0 then error "expected zero module";
            continue;
            );
*-
        inds#i => comps#i
        );
    directSum compsLabelled
    )

flattenBlocks Matrix := (M) -> (
    F := flattenBlocks target M;
    G := flattenBlocks source M;
    map(F,G,matrix M)
    )

displayBlocks = method()
displayBlocks Matrix := (M1) -> (
    M := flattenBlocks M1;
    src := select(indices source M, i-> i =!= null);
    tar := select(indices target M, i-> i =!= null);
    netList (prepend(
        prepend("", src),
        for t in tar list prepend(t, for s in src list (
                mts := M^[t]_[s];
                h := if mts == 0 then "." else if (numrows mts == numcols mts and mts == 1) then "1" else net mts
                ))
        ), Alignment=>Center)
    )

labels := method()
labels Module := List => M -> (
    if M.cache#?"label" then M.cache#"label" else
      if M.cache.?components then (
	L := M.cache.components;
	if not (L_0).cache#?"label" then error"no labels" else
--	  for N in M.cache.components list N.cache#"label")
	  apply(M.cache.components, N ->  N.cache#"label"))
    )

    

///
restart
debug loadPackage("AInfinity", Reload =>true)
time bSymbols(10,10,20);


pdR = 3;pdM=3
d =5
///


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


eagonSymbols = method()
eagonSymbols(ZZ,ZZ) := List => (n,i) ->(
    --symbol of the module Y^n_i, as a list of pairs, defined inductively from n-1,i+1 and n-1,0
    --assumes large number of vars and pd.
    if n === 0 then return {(i,{})};
    if i === 0 then return eagonSymbols(n-1,1);
    e' := eagonSymbols (n-1,0);
    e'1 := apply (e', L -> L_1|{i});
    eagonSymbols(n-1,i+1)|apply (#e', j-> (e'_j_0,e'1_j))
    )
 -*

bSymbols ZZ := List => n -> (
    --these are indexed with the module resolution component last, 
    --and the ring resolution component indexed as in the B complex: A_i = B_(i+1) for i>= 1.
    --note that the symbol is now a single list
    L :=eagonSymbols(n,0);
    apply(L, ell -> toList flatten(ell_1/(i->i+1), ell_0))
)

    if n === 0 then return {0};
    bS' := bSymbols n-1;
    apply(bS', s -> toList flatten

	)

bSymbols(ZZ,ZZ,ZZ) := List => (pdA,pdM,n) -> (
    L := bSymbols n;
    select(L, ell -> (
	    ell' := drop(ell, -1);
	    all(ell', u -> u <= pdA+1) and last ell <= pdM))
    )
*-
	  


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


tensor(Ring, List) := o -> (R,L) -> (
    --note that A**B**C**..**D = (((A**B)**C)**..**D) = tensor(R,{A..D}).
    --The order matters for chain complexes; maybe not for modules.
    --
    if L === {} then return R^1;
    if #L === 1 then return L_0;
    ans1 := tensor(R,drop(L,-1));
    ans1**last L
    )

    


///
restart
loadPackage"AInfinity"

S = ZZ/101[x,y]
K = complex koszul matrix{{x^2,y^3}}

K**K
(components (K**K**K)_3)_2
components oo

assert(K**K**K != K**(K**K))
assert(K**K**K == (K**K)**K)
assert (source tensorAssociativity(K,K,K) == K**(K**K))
assert (not source tensorAssociativity(K,K,K) == (K**K)**K)

apply(length (K**K**K), i->((K**K)**K).dd_(i+1) - (K**(K**K)).dd_(i+1))

t = (A,B,C) -> tensorAssociativity(A,B,C)
s = method()
s(Module, Module, Module) := Matrix => (A,B,C) -> (tensorAssociativity(A,B,C)^-1
s(ChainComplex, ChainComplex, ChainComplex) := ChainComplexMap => (A,B,C) -> (
    D := (A**B)**C;
    E := A**(B**C);
    ta := tensorAssociativity(A,B,C);
    map(D,E,for i from min D to max D do 
	for 
    C0 = A**B**C;
    C1 = A**(B**C);
    F0 := tensorAssociativity(A_0,B_0,C_0);
    extend(id_C0//F0, C1)

    
    

(K**K)**((K**K)**K) == (K**K)**(K**K**K)
(K**K)**((K**K)**K) != (K**K)**K**K**K
Goal = (K**(K**K)**K) 
G1 = (K**K)**(K**K) 
G1 == (K**K**(K**K))
G2 = K**(K**(K**K))
Start = (((K**K)**K)**K) 
target t(K**K,K,K) == Start
source t(K**K,K,K) == G1
target t(K,K,K**K) == G1
source t(K,K,K**K) == G2
target (id_K**s(K,K,K)) == G2

///


TEST///
S = ZZ/101[a,b]
A = koszul vars S
B = koszul matrix{{a^2,b^3}}
C = koszul matrix{{b^4,a^5}}
assert(A**B**C == tensor(S,{A,B,C}))
assert(tensor(S,{C,B,A}) != tensor(S,{A,B,C}))

(((A**B)**C)**D) <-(A**B)**(C**D)<-A*(B*(C**D)) <- A*((B*C)*D)
tensorAssociativity(A*B,C,D)
tensorAssociativity(A,B,C**D)
id_A**tensorAssociativity(B,C,D)

A1*A2*....*An -- (A1*..*Ap)*((Ap'*..Aq)*(Aq..An)) = (A1*..*Ap)*(Ap'*..Aq*Aq'*..*An)
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
    --F = freeResolution I
    --K = freeResolution MS
    R := ring M;
    p := presentation R;
    S := ring p;
    phi1 := substitute(presentation M, S);
    phi := phi1 | target phi1 ** p;
    MS := prune coker phi;
    K := freeResolution MS;
    F := freeResolution coker p;
    golodBetti(F,K,b)
    )




-*
burck = method()
burck(HashTable,HashTable,ZZ) := Complex => (mR,mM,n) ->(
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
   
   A = freeResolution M; betti A
   B = (complex apply(length A - 1, i -> -A.dd_(i+2)))[-2];
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

uninstallPackage "Complexes"
restart
installPackage "Complexes"
viewHelp Complexes

t = tensorAssociativity(B_2, B_2, B_2);
b = betti B
b ** b
(b ** b) ** b  ==
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


-*
TODO: 

Make aInfinity(Ring,ZZ) use the commutative multiplication. 
Is there an analogue for the higher products?
can we call SchurComplexes?

add the maps B -> G 

replace ** with eTensor

add associativities

construct the resolution




Note: from "Grammarly":
"Labeled and labelled are both correct spellings, 
and they mean the same thing. 
How you spell the word depends on your audience. 
If you are writing for American readers, labeled is the preferred spelling. 
In other places, such as Great Britain and Canada, 
labelled is a more common spelling than labeled."

also: labeled gets 5X more hits in google than labelled.

*-
S = ZZ/101[a,b,c]
B = apply(4, i-> S^{1+i:i})
A = B_0**B_1**(B_2++B_3)
formation (A.cache.formation#1#1)
oo.cache.indices
A.cache.indices 


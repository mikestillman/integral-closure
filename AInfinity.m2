
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
--    "LabeledModule",
--    "LabeledComplex",
--    "LabeledChainComplex",
--    "labeledModule",
--    "getLabel",
--    "labeledComplex",
--    "labeledChainComplex",
    --symbols
--    "label",
--    "factors",
--    "module",
    "symbolPairs",
--
    "aInfinity",
    "burck",
    "golodBetti",
    "labeledTensorComplex"
    }


-*
currently (11/26) BurkeData produces a list of the free modules in the Burke resolution to stage n,
in a form that F_5^[{3,2,0}] works (this is the projection).

Next to do: a function that takes a symbol {u_1..u_s} and produces all the 
lists
{offset, width, source symbol} = {p,w,{u_1..u_s}}
corresponding to maps from that free module:
a map from
{u_1..u_s}, Where u_i is the index of a module in B for i<s and u_s of a module in G;
to
(-1)^(sum{u_1..u_p},{u_1..u_p,sum(u_(p+1)..u_(p+w)),u_(p+w+1)..u_s}
gotten by applying m#{w,{u_(p+1)..u_(p+w)}}

Could we speed up BurkeData by creating the tensor products inductively?
*-

///
uninstallPackage "AInfinity"
restart
installPackage "AInfinity"
///
burkeData = method()
burkeData(Ring,Module,ZZ) := List => (R,M,n) ->(
--currently (11/26) 
--F = burkeData(R,M,6) 
--produces the list of the free modules indexed 0..n in the Burke resolution,
--in a form that things like F_5^[{3,2,0}] work (this is the projection).

S := ring presentation R;
RS := map(R,S);
G := labeledTensorComplex freeResolution(pushForward(RS, M), LengthLimit=>n);
A' := freeResolution (coker presentation R, LengthLimit => n-1);
A'' := labeledTensorComplex(A'[-1]);
A := A''[1];
B0 := complex(apply(length A-1, i-> A.dd_(i+2)))[-2];
BB := {G}|apply(n//2, i->labeledTensorComplex(toList(i+1:B0)|{G}));
C := apply(n+1, i-> select(apply(BB,b-> b_i), c -> c != 0));
apply(C, c -> labeledDirectSum c)
    )

labeledDirectSum = method()
labeledDirectSum Module := Module => M ->(
    ci := componentsAndIndices M;
    directSum apply(#ci_0, i->(ci_1_i => ci_0_i))
    )
labeledDirectSum List := Module => L ->(
    ciL := apply(L, M -> componentsAndIndices M);
    directSum flatten apply(ciL, ci -> apply(#ci_0, i->(ci_1_i => ci_0_i)))
    )

mapComponents = method()
mapComponents List := List => u -> (
    --u = {u_0..u_n}; for i<n, u_i represents a free module in B, the truncated, shifted res of R^1; 
    --u_n represents a free module in G, the S-resolution of the R-module M.
    --output is a list whose elements have the form {sign, p,q,{v_0..v_m}} corresponding to
    --a map collapsing u_p..u_q to sum(for i from p to q list u_i), where sign is (-1)^sum(apply p, i->u_i).
    --We require also v_0..v_(m-1)>=2 and v_m>=0; otherwise this is not a free module.
    sign := p-> (-1)^(sum apply(p, i->u_i));
    n := #u-1;
    L0 := apply(n+1, p-> {sign p, p,p,u_{0..p-1}|{u_p-1}|u_{p+1..n}});
    L1 := flatten apply(n+1, p -> for q from p+1 to n list {sign p, p,q,u_{0..p-1}|
	                         {-1+sum for i from p to q list u_i}|
		                 u_{q+1..n}});
    L := L0|L1;
    select(L, LL -> all(#LL_3, i -> if i<n then LL_3_i>=2 else LL_3_i>=0))	
    )

mapComponents(HashTable, HashTable, ZZ) := List =>(mA,mG,n) ->(
    --List the matrices of the maps starting from 
    --the component labeled u in 
    --B**..**B**G, with n = #u-1 copies of B.
    R := mA#"ring";
    B := mA#"resolution";
    M := mG#"module";
    G := mG#"resolution";
    F := burkeData(R,M,n);

    for t from 1 to #F+1 list (
	c :=componentsAndIndices F_t;
	for s from 0 to #c_0 list(
	    u := c_1_s;
    	    n := #u-1;
    	    vv := mapComponents u;
    	    for v in vv list (
		sign := v_0;
		p := v_1;
		q := v_2;
--need to tensor the folowing with R
		map(F_(t-1), F_t, 
		    (F_(t-1))_[u_{0..p-1}|{-1+sum u_{p..q}}|u_{q+1..n}] * 
		    if q<n 
		    then sign * (
	 		tensor (S, for i from 0 to p-1 list B_(u_i))**
	 		mA#{q-p+1, u_{p..q}}**
	 		tensor(S, for i from p+1 to n-1 list B_(u_i))**
	 		G_(u_n))
                    else sign * (
	     		tensor(S, for i from 0 to p-1 list B_(u_i))**
	     		mG#{q-p+1, u_{p..q}}))
             ))
    ))

burke = method()
burke(HashTable,HashTable,List) := Complex => (mA,mG,F) ->(
    (for j from 1 to #F-1 list (
	ci := componentsAndIndices F_j))
)
	
    
///
restart
debug loadPackage("AInfinity", Reload => true)
u = {2,1}
netList mapComponents u

sign := p-> (-1)^(sum apply(p, i->u_i))
apply(5, p -> sign (p)
-1^sum apply(0, i->u_i)


restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R = S/(ideal vars S)^2
R1 = S^1/(ideal vars S)^2
M = coker vars R
mA = aInfinity(R,3)
mG = aInfinity(mA,M,3)
u = {3,1}
n = 3
mapComponents (mA,mG,n)

netList mapComponents u
F =  burkeData(R,M,6)
componentsAndIndices F_5

--
A = freeResolution R1
freesA = AFrees(A,5)
X = freesA#{2}++freesA#{3,2}

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


suitable = method()
suitable List := v-> 
     -- v is a list of ZZ. returns null unless v has the form
     -- {0...0,1,0..0}, in which case it returns the position of the 1.
                  if min v == 0 then position (v, vv -> vv == 1) else null;
		  
labeler = (L,F) -> directSum(1:(L=>F));


///
restart
debug loadPackage("AInfinity", Reload => true)
///

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
    Max := apply(L, C->max C);
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
                   (complex d)[-sum(L, ell -> min ell)]
		   )
labeledTensorComplex Complex := Complex => C -> labeledTensorComplex{C}

lTC = labeledTensorComplex;

///
restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R1 = S^1/ideal(a,b)
A = (freeResolution R1) [-3]
lTC{A,A,A}
A**A**A
lTC{A,A}
A**A

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
m#"ring" = R;
S := ring presentation R;
RS := map(R,S);
A' := freeResolution coker presentation R;
A'' := labeledTensorComplex(A'[-1]);
A := A''[1];

B := complex(apply(length A-1, i-> A.dd_(i+2)))[-2]; -- this was called B0
-*
B1 := complex(for i from 3 to length B0+2 list 
	map(B0_(i-1),
	    B0_i,
	    B0.dd_i));
--B := labeledTensorComplex{B1[-2]};
B := B1[-2];
*-
m#"resolution" = B;

--m#{1,i}
apply(length B , i-> m#{1,{i+3}} = B.dd_(i+3));

--m#{2,i}


A0 := (complex S^1)[-2];
d := map(A0, B, i-> if (i == 2) then A.dd_1 else 0);
m#"Bmap" = d;
B2 := labeledTensorComplex{B,B};
--elapsedTime N := nullHomotopy (d**id_B-id_B**d);-- this is SLOW! -- 19 sec

--fix the nullhomotopy problem!
A0':=chainComplex A0;
B2':=chainComplex B2;
B' := chainComplex B;
d' := map(A0', B', i-> if (i == 2) then A'.dd_1 else 0);
N := nullhomotopy (d'**id_B'-id_B'**d'); -- .066 sec compared to 19
--end of fix

for i from 2*min B to max B+1 do (
	(C,K) := componentsAndIndices (B2_i); 
	for j from 0 to #K -1 do 
	  if target N_i !=0 then
	     m#{2,K_j} = map(B_(sum K_j - 1),C_j, N_(i)*((B2_i)_[K_j]))
       );
--m#{3,i}	                    
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
m#"module" = M;
B := mR#"resolution";
R := ring M;
S := ring presentation R;
RS := map(R,S);

-*
MS := pushForward(RS,M);

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
--B = mR#"resolution" -- use this if we take mR as an input.
*-

G0 := freeResolution pushForward(RS,M);
G := complex labeledTensorComplex{G0};
m#"resolution" = G;

--m#{1,i}
  apply(length G , i-> m#{1,{i+1}} = G.dd_(i+1));    

--m#{2,i} 
BG := labeledTensorComplex{B,G};
d0 := dual syz dual B.dd_3;
m20 := map(S^1**G_0, B_2**G_0, d0**G_0)//G.dd_1; 
G' := naiveTruncation(G,1,infinity);
m2 := extend(G',BG,m20,-1);
--for i from min BG to max G+1 do
--   m#{2,i} = map(G_(i-1),BG_i, m2_i);

for i from min B to max BG do (
	(C,K) := componentsAndIndices (BG_i); 
	for j from 0 to #K -1 do 
	  if target m2_i !=0 then
	     m#{2,K_j} = map(G_(sum K_j - 1),C_j, m2_(i)*((BG_i)_[K_j]))
       );

--m#{3,i}	                       );
B2G := labeledTensorComplex (toList(2:B)|{G});
e := apply(3, ell -> toList(ell:0)|{1}|toList(3-ell-1:0));
for i from min B2G to max G+1 do(
	(C,K) := componentsAndIndices (B2G_i);
	for k in K do(
	dm3 := m#{2,{sum k_{0,1}-1,k_2}} * (mR#{2,k_{0,1}}**G_(k_2)) +
	
	       -1^(k_0)* m#{2,{k_0,sum k_{1,2}-1}} * (B_(k_0)**m#{2,k_{1,2}}) +
	               
	       sum(apply(#e, ell -> if min(k-e_ell)< min B then 0 else 
		       -1^(sum k_{0..ell-1})*m#{3,k-e_ell}*m#{1,k}));

	m3 := dm3//G.dd_(i-1);
        m#{3,k} = map(G_(i-1), source ((B2G_i)_[k]), m3))
     );
hashTable pairs  m)

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



///
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "Complexes"
kk = ZZ/101
S = kk[x_1..x_4]
R = S/(ideal vars S)^2 -- a golod ring
F = res coker vars R
M = coker F.dd_4;
elapsedTime mR = aInfinity(R,3);
elapsedTime m = aInfinity(mR,M,3);
K = sort select(keys m, k->class k === List)
for k in K do <<k<<" "<< picture(m#k)<< betti m#k <<endl;

MS = pushForward(map(R,S), M)
G = res MS
A = res coker presentation R

///

///
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "Complexes"
kk = ZZ/101
S = kk[x_1..x_4]
R = S/(ideal vars S)^2
H = aInfinity(R,3);
K = sort select(keys H, k->class k === List)
for k in K do <<k<<" "<< picture(H#k)<< betti H#k <<endl;
H#{2,{2,4}}

use S
R = S/ideal(apply(gens S, p-> p^2))
H = aInfinity(R,3);
K = sort select(keys H, k->class k === List)
for k in K do <<k<<" "<< picture(H#k)<< betti H#k <<endl;

--note that m{3,{2,2,2}} = 0, since K res R^1 is a DG algebra!

A = freeResolution coker presentation R
--elapsedTime lTC{A,A,A} 
--elapsedTime A**A**A -- this is too slow

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

tensorDegrees = method()
tensorDegrees List := List => L -> (
    --L is a list of lists of ZZ. If L_i is the list of degrees of
    --a free module F_i, where F is a list of free modules,
    --then the output is a list of the degrees
    --of the free module tensor F.
    n := #L;
    if n ==0 then return {0};
    if n == 1 then return L_0;
    M := tensorDegrees drop(L, 1);
    flatten apply(L_0, ell -> apply(M, m-> ell+m))
    )

///
restart
debug loadPackage "AInfinity"
V = ZZ/101[x_1..x_3]
R = V/(ideal vars V)^3
R1 = V^1/(ideal vars V)^3
M = R**coker vars V
golodRanks(M,6)
betti res (M, LengthLimit =>6)
F = res M
N = coker F.dd_2
golodRanks(coker (F.dd_2),6)
res (N, LengthLimit =>6)
 ///    

golodRanks = method()
golodRanks (Module,ZZ) := List => (M,b) ->(
    --M is a module over a factor ring R = S/I, S a polynomial ring.
    --implements the rational function as power series. 
    --See Avramov, six lectures, p.50.
    --Out put is the sequence of ranks, equal to those in the free resolution
    --if and only if M is a Golod module.
    expand := (nu,de,n) -> nu*sum(apply(n, i-> (de)^i)); --nu/(1-de) as power series
    R := ring M;
    p := presentation R;
    S := ring p;
    RS := map(R,S);
    MS := prune pushForward(RS,M);
    G := res MS;
    A := res coker p;
    x := symbol x;
    U := QQ[x];
    g := sum(1+length G, i-> x^i*rank G_i);
    a := sum(toList(1..length A), i-> x^(i+1)*rank A_i);
    c := (coefficients expand(g,a,b))_1;
    (reverse flatten entries c)_(toList(0..b))
    )






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

labeledTensorChainComplex = method()
labeledTensorChainComplex List := ChainComplex => L -> (
    --L = {C_0..C_(p-1)}, list chain complexes. Form the tensor product of the C_i
    --in such a way that if the tensor products of the modules (C_i)_m are labeled,
    --then the modules of the tensor product are direct sums of modules from the hashtable, so that
    --componentsAndIndices applied to pC gives the correct list of indices, and
    --thus picture pC.dd_m works.
    if class L_0 =!= ChainComplex then error"Input should be a list of ChainComplexes.";
    S := ring L_0;
    if #L == 1 and class L_0 === ChainComplex then (
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
                   (chainComplex d)[-sum(L, ell -> min ell)])
B
G
labeledTensorChainComplex{chainComplex B,chainComplex G}
labeledTensorComplex{B,G}
B**G
lTC{B,G}
lTC{G,G}
G**G
lTC{B,B}
B**B
lTC{B,B,G}
B**B**G

----------
--Roos example: non-Golod with trivial homology algebra.
restart
needsPackage "DGAlgebras"
debug needsPackage "AInfinity"
kk = ZZ/101
--kk = QQ
S = kk[x,y,z,u]
I = ideal(u^3, x*y^2, (x+y)*z^2, x^2*u+z*u^2, y^2*u+x*z*u, y^2*z+y*z^2) -- has the betti nums as in Roos
betti (A = res I) -- shows that the m_2 must be trivial
R = S/I
isGolod R -- gives the wrong answer! as one sees by comparing Poincare series, below
H = acyclicClosure(R, EndDegree => 0)
isHomologyAlgebraTrivial H

betti res( coker vars R, LengthLimit =>5)
--golodRanks(coker vars R, 5)
((1+t)^4)*sum(10, i-> (6*t^2+12*t^3+9*t^4+2*t^5)^i)

m = aInfinity(R,3);
trim ideal(m#{3,{2,2,2}})

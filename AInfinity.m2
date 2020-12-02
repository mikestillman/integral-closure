
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
    "aInfinity",
    "burck",
    "golodBetti",
    "labeledTensorComplex",
    "labeledDirectSum",
    "mapComponents"
    }


-*
currently (11/26) BurkeData produces a list of the free modules in the Burke resolution to stage n,
in a form that F_5^[{3,2,0}] works (this is the projection).

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
--Output is a list of labeled complexes of R-modules
S := ring presentation R;
RS := map(R,S);
MS := pushForward(RS,M);
G := labeledTensorComplex freeResolution(MS, LengthLimit => n);
A' := freeResolution (coker presentation R, LengthLimit => n-1);
A'' := labeledTensorComplex(R**A'[-1]);
A := A''[1];
B0 := complex(apply(length A-1, i-> A.dd_(i+2)))[-2];
BB := {G}|apply(n//2, i->labeledTensorComplex(toList(i+1:B0)|{G}));
C := apply(n+1, i-> select(apply(BB,b-> b_i), c -> c != 0));
apply(C, c -> labeledDirectSum c)
    )

burkeData(Module,ZZ) := List => (M,n) ->(
--currently (11/26) 
--F = burkeData(R,M,6) 
--produces the list of the free modules indexed 0..n in the Burke resolution,
--in a form that things like F_5^[{3,2,0}] work (this is the projection).
--output is a list of labeled complexes of S-modules, where 
--S = ring presentation ring M.
R := ring M;
S := ring presentation R;
RS := map(R,S);
G := labeledTensorComplex freeResolution(pushForward(RS, M), LengthLimit=>n);
A' := freeResolution (coker presentation R, LengthLimit => n-1);
A'' := labeledTensorComplex(A'[-1]);
A := A''[1];
B0 := labeledTensorComplex complex(apply(length A-1, i-> A.dd_(i+2)))[-2];
BB := {G}|apply(n//2, i->labeledTensorComplex(toList(i+1:B0)|{G}));
C := apply(n+1, i-> select(apply(BB,b-> b_i), c -> c != 0));
apply(C, c -> labeledDirectSum c)
    )
///
restart
debug loadPackage "AInfinity"
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
M = coker vars R
n = 3
BB = burkeData(M,n)
netList apply(BB, X -> componentsAndIndices X)
B3 = BB_3
B3_[{2,1}]
componentsAndIndices B3
///

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
--    L
    select(L, LL -> all(#LL_3, i -> if i<#LL_3-1 then LL_3_i>=2 else LL_3_i>=0))	
    )

///
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "Complexes"
S = ZZ/101[a,b,c]
K = complex koszul vars S
KK = labeledTensorComplex{K,K}
componentsAndIndices KK_5
R = S/ideal a
picture labeledTensorComplex(R,KK)
///

mapComponents(HashTable, HashTable, ZZ) := List =>(mA,mG,len) ->(
    --List the matrices of the maps starting from 
    --the component labeled u in 
    --B**..**B**G, with n = #u-1 copies of B.
    R := mA#"ring";
    S := ring presentation R;
    B := mA#"resolution";
    M := mG#"module";
    G := mG#"resolution";
    F := burkeData(R,M,len);

    for t from 1 to len list (
	c :=componentsAndIndices F_t;
	flatten apply(#c_0, s->(
	    u := c_1_s;
    	    n := #u-1;
    	    vv := mapComponents u;
    	    for v in vv list (
		sign := v_0;
		p := v_1;
		q := v_2;
		map(F_(t-1), F_t, 
		    (F_(t-1))_[u_{0..p-1}|{-1+sum u_{p..q}}|u_{q+1..n}]*
		    (if q<n 
		    then sign * (
	 		tensor (S, for i from 0 to p-1 list B_(u_i))**
	 		mA#{q-p+1, u_{p..q}}**
	 		tensor(S, for i from q+1 to n-1 list B_(u_i))**
	 		G_(u_n)
			    	)
                    else sign * (
	     		tensor(S, for i from 0 to p-1 list B_(u_i))**
	     		mG#{q-p+1, u_{p..q}}
			        )
		    )*
		    (F_t)^[u])
             ))))
    )

burke = method()
burke(HashTable,HashTable,List) := Complex => (mA,mG,F) ->(
    (for j from 1 to #F-1 list (
	ci := componentsAndIndices F_j))
)
	
    
///


restart
debug loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R = S/(ideal vars S)^2
R = S/ideal(apply(gens S, x -> x^3))
M = coker vars R
mA = aInfinity(R,3)
mG = aInfinity(mA,M,3)
B = mA#"resolution"
G = mG#"resolution"
BG = labeledTensorComplex{B,G}
picture BG.dd_5
RBG = R**BG
picture RBG_5
components BG.dd_5
ci = componentsAndIndices BG_5
formation RBG_5

elapsedTime netList (D =  mapComponents (mA,mG,n));
C = complex apply(D, d-> sum d)
netList for i from 1 to 3 list picture C.dd_i
C
C.dd^2
displayBlocks C.dd_2, displayBlocks C.dd_3
displayBlocks (C.dd_2*C.dd_3)

netList apply(keys mA, k-> (k, mA#k))
netList apply(keys mG, k-> (k, mG#k))
C.dd_2, C.dd_3
///

labeler = method()
labeler(Thing,Module) := (L,F) -> directSum(1:(L=>F));
labeler(List, List) := Module => (Modules, Labels) ->(
    --forms the direct sum of the Modules, with the components labeled by the Labels.
--    directSum apply(#Modules, i -> (Labels_i => Modules_i))
    apply(#Modules, i -> labeler(Labels_i, Modules_i))
	)
    
label = method()
label(Module) := Thing => M-> (indices M)_0
label(List) := List => L-> apply(L, M ->(indices M)_0)

///
restart
debug loadPackage"AInfinity"
S = ZZ/101[a,b]
labeler({S^1,S^2},{A,B})
directSum oo
componentsAndIndices oo
///

labeledDirectSum = method()
labeledDirectSum Module := Module => M ->(
    ci := componentsAndIndices M;
    directSum apply(#ci_0, i->(ci_1_i => ci_0_i))
    )

labeledDirectSum(Ring, Module) := Module => (R,M) ->(
    ci := componentsAndIndices M;
    directSum apply(#ci_0, i->(ci_1_i => R**ci_0_i))
    )

labeledDirectSum List := Module => L ->(
    ciL := apply(L, M -> componentsAndIndices M);
    directSum flatten apply(ciL, ci -> apply(#ci_0, i->(ci_1_i => ci_0_i)))
    )

labeledTensorComplex = method()
labeledTensorComplex List := Complex => L -> (
    --L = {C_0..C_(p-1)}, list chain complexes. Form the tensor product D of the C_i
    --in such a way that the tensor products of the modules (C_i)_(m_i) are labeled {..m_i..}
    --so that componentsAndIndices applied to C_i gives the correct list of indices, and
    --thus picture C.dd_m works.
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
	    apply(com, co -> co => labeler(co, tensor(S,apply(p, pp->(L_pp)_(co_pp)))))
	    ));
    modules = select(modules, tt-> #tt != 0);

suitable := v-> if min v == 0 then position (v, vv -> vv == 1) else null;
     -- v is a list of ZZ. returns null unless v has the form
     -- {0...0,1,0..0}, in which case it returns the position of the 1.

D := apply(modules, L -> directSum L);
--if L is a singleton and L_0 is labeled, then directSum L loses the label!

    d := for i from 0 to #modules -2 list(
        map(D_i, D_(i+1),
            matrix table( -- form a block matrix
                modules#i, -- rows of the table
                modules#(i+1), -- cols of the table
                (j,k) -> ( -- j,k are each labeled modules
		    indtar := j_0_0
		    indsrc := k_0_0;	    
                    tar := j;
                    src := k;
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

labeledTensorComplex(Ring, Complex) := Complex => (R,C)->(
    --preserve the labels on C while tensoring each free module with R
    c := for i from min C to max C list componentsAndIndices C_i;
    D := for j from min C to max C list if #c_j_0 === 1 then 
    --this is to fix the directSum bug
        labeler(c_j_1_0, R**c_j_0_0) else
    	directSum apply(#c_j_0, i -> labeler(c_j_1_i, R**c_j_0_i));
    complex for i from 1+min C to max C list map(D_(i-1),D_i,R**C.dd_i)
    )
	
lTC = labeledTensorComplex;
///
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "Complexes"
S = ZZ/101[a,b,c]
K' = complex koszul vars S
K = lTC K'
picture (K2 = labeledTensorComplex{K,K})
componentsAndIndices(K2_3)
(K2_3)_[{3,0}]

L = {K,K}
R = S/ideal a
picture labeledTensorComplex(R,KK)

restart
debug loadPackage("AInfinity", Reload => true)

C = labeler(A,S^1) ++ labeler(B,S^2)
componentsAndIndices C
picture id_C
--but
C_[A]
--does not work!

C = (A =>labeler(A,S^1)) ++ (B =>labeler(B,S^2))
componentsAndIndices C
picture id_C
--work, AND
C_[A] -- works

C = (A =>S^1) ++ (B => S^2)
componentsAndIndices C -- does not work
picture id_C -- does not work
--but
C_[A] -- works


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

K = koszul vars S
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
elapsedTime N := nullHomotopy (d**id_B-id_B**d);-- this is SLOW! -- 19 sec
-*
--fix the nullhomotopy problem!
A0':=chainComplex A0;
B2':=chainComplex B2;
B' := chainComplex B;
d' := map(A0', B', i-> if (i == 2) then A'.dd_1 else 0);
N := nullhomotopy (d'**id_B'-id_B'**d'); -- .066 sec compared to 19
--end of fix
*-
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

///--the fix
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "CompleteIntersectionResolutions"
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
M = coker vars R
mA = aInfinity(R,3)
mG = aInfinity(mA,M,3)
A = res coker presentation R
G = res pushForward((map(R,S)),M)
AG = A**G
m0 = map(G_0, AG_0, 1)
mm = extend(G,AG,m0)
indices G
m2 = mm_2*(AG_2)_[(1,1)]
mG = new MutableHashTable from mG
mG#{2,{2,1}}
mG#{2,{2,1}} = m2
mG = hashTable pairs mG

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

G0 := freeResolution pushForward(RS,M);
G := complex labeledTensorComplex{G0};
m#"resolution" = G;

--m#{1,i}
  apply(length G , i-> m#{1,{i+1}} = G.dd_(i+1));    

--m#{2,i} --m#{2,{2,1}} is still wrong!
m2 := new MutableHashTable;-- m2#i will be a map to G_i
BG := labeledTensorComplex{B,G};
A0 := complex {S^1};
AG := labeledTensorComplex{A0,G};
m2#1 = map(AG_0, BG_2, (dual syz dual B.dd_3)**G_0)//AG.dd_1;
for i from 2 to max AG do m2#i = -(m2#(i-1)*BG.dd_(i+1))//AG.dd_i;

for i from 1 to max G do (
	(C,K) := componentsAndIndices (BG_(i+1)); 
	for j from 0 to #K -1 do 
	  if target m2#i !=0 then
	     m#{2,K_j} = map(G_i,C_j, (m2#i)*((BG_(i+1)_[K_j])))
       );
--error(); --m2#2 is wrong.
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

///--bug!
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "Complexes"
kk = ZZ/101
S = kk[a,b]
R = S/ideal"a3,b3"
M = coker vars R
koszul(2, vars R)
mA = aInfinity(R,3)
mG = aInfinity(mA,M,3)
--The following should be 0 and it's not:
--m2#2
--koszul(2,vars R)*m2#2
B = mA#"resolution"
G = mG#"resolution"
--The following should be the composite 
--0 == map B_2**G_1 -> G_2++B_2**G_0 -> G_1
G.dd_2*mG#{2,{2,1}}+
   mG#{2,{2,0}}* (B_2**mG#{1,{1}})
--and should thus be in (a3,b3,c3).
mG#{2,{2,0}}
G.dd_2*mG#{2,{2,1}}
keys mG
///
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

picture = method()
picture Matrix := (M1) -> (
    M := flattenBlocks M1;
    src := indices source M;
    tar := indices target M;
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
picture Module := M -> picture id_M
picture Complex := C -> netList apply(toList(min C+1..max C), i-> picture C.dd_i)
picture ChainComplex := C -> netList apply(toList(min C+1..max C), i-> picture C.dd_i)

flattenBlocks = method()
flattenBlocks Module := (F) -> (
    if not isFreeModule F then error "expected a free module";
    (comps, inds) := componentsAndIndices F;
    compsLabelled := for i from 0 to #comps-1 list (
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
	  apply(M.cache.components, N ->  N.cache#"label"))
    )

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
    --Output is the sequence of ranks, equal to those in the free resolution
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

suitable := v-> if min v == 0 then position (v, vv -> vv == 1) else null;
     -- v is a list of ZZ. returns null unless v has the form
     -- {0...0,1,0..0}, in which case it returns the position of the 1.

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

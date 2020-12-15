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
	PackageExports => {"Complexes", "DGAlgebras"},
        Headline => "Compute AInfinity structures on free resolutions",
        DebuggingMode => true
	)

export {
    "aInfinity",
    "burke",
    "golodBetti",
    "labeledTensorComplex",
    "labeledDirectSum",
    "mapComponents",
    "componentsAndIndices",
    "label",
    "picture",
    "displayBlocks",
    "extractBlocks"
    }

///
restart
uninstallPackage "AInfinity"
restart
installPackage "AInfinity"
check AInfinity
restart
debug loadPackage "AInfinity"
///

///
restart
loadPackage("AInfinity", Reload => true)
kk = ZZ/5
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c)) -- a simple 3 variable Golod ring
K = koszul vars R
M = coker K.dd_2
E = burke(R,M,5)
E.dd^2
apply(length E, i-> prune HH_(i)E)
picture E
betti E.dd_4
///

burke = method()
burke(Ring, Module, ZZ) := Complex => (R,M,len) ->(
    --put the map components together into what should be a complex.
    mA := aInfinity(R,3);
    mG := aInfinity(mA,M,3);
    D := mapComponents(mA,mG,len);
    labeledTensorComplex(R,complex(D/sum))
    )


-*
currently (11/26) BurkeData produces a list of the free modules in the Burke resolution to stage n,
in a form that F_5^[{3,2,0}] works (this is the projection). note that this duplicates 	   
some of the slowest parts of the two aInfinity routines, and should be combined
with them.

Could we speed up BurkeData by creating the tensor products inductively?
*-

burkeData = method()
burkeData(Module,ZZ) := List => (M,n) ->(
--currently (11/26) 
--F = burkeData(M,n) 
--produces the list of the free modules indexed 0..n in the Burke resolution,
--in a form that things like F_5^[{3,2,0}] work (this is the projection).
--output is a list of labeled S-modules, where 
--S = ring presentation ring M.
R := ring M;
S := ring presentation R;
RS := map(R,S);
G := labeledTensorComplex freeResolution(pushForward(RS, M), LengthLimit=>n);
A' := freeResolution (coker presentation R, LengthLimit => n-1);
A'' := labeledTensorComplex(A'[-1]);
A := A''[1];
--B0 := labeledTensorComplex complex(apply(length A-1, i-> A.dd_(i+2)))[-2];
B0 := labeledTensorComplex complex(apply(length A-1, i-> -A.dd_(i+2)),Base =>2);
BB := {G}|apply(n//2, i->labeledTensorComplex(toList(i+1:B0)|{G}));
C := apply(n+1, i-> select(apply(BB,b-> b_i), c -> c != 0));
apply(C, c -> labeledDirectSum c))

///
restart
debug loadPackage "AInfinity"
S = ZZ/101[a,b,c]
R = S/ideal"a3,b3,c3"
M = coker vars R
n = 4
BB = burkeData(M,n)
netList apply(BB, X -> componentsAndIndices X)
B3 = BB_3
B3_[{2,1}]
///

mapComponents = method()
mapComponents List := List => u -> (
    --u = {u_0..u_n}; for i<n, u_i represents a free module in B, the truncated, shifted res of R^1; 
    --u_n represents a free module in G, the S-resolution of the R-module M.
    --output is a list whose elements have the form 
    --{sign, p,q,{v_0..v_m}} corresponding to
    --a map with
    --target =  {v_0..v_m} = {u_0..u_(p-1), v_p, u_(q+1)..u_n}
    --that collapses
    --u_p..u_q to a single index v_p = -1+sum(for i from p to q list u_i), 
    --where sign is (-1)^sum(apply p, i->u_i).
    --We require also v_0..v_(m-1)>=2 and v_m>=0; otherwise this is not 
    --the index of a module in the resolution.

    sign := p-> (-1)^(sum apply(p, i->u_i)); 
    n := #u-1;
    L0 := apply(n+1, p-> {sign p, p,p,u_{0..p-1}|{u_p-1}|u_{p+1..n}});
    L1 := flatten apply(n, p -> for q from p+1 to n list {sign p, p,q,u_{0..p-1}|
	                         {-1+sum for i from p to q list u_i}|
		                 u_{q+1..n}});
    L := L0|L1;
    select(L, LL -> all (drop(LL_3,-1), p -> p >= 2) and last LL_3 >= 0)
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
    --The output is a list D_1..D_len
    --where D_t is a list of  the matrices of maps 
    --F_t ->comp(u,F_t) -> comp(v, F_(t-1) -> F_(t-1)
    --where comp(u,F_t) is the component of F_t labeled u
    --and similarly for v,F_(t-1).
    --Thus sum D_t will be the map F.dd_t in the Burke resolution.
    R := mA#"ring";
    S := ring presentation R;
    B := mA#"resolution";
    M := mG#"module";
    G := mG#"resolution";
    F := burkeData(M,len); -- the list of labeled free modules

   --Now form the components of the maps. 

      for t from 1 to len list (
  
   --First construct vv, the list of valid maps F_t --> F_(t-1).
	c :=componentsAndIndices F_t;
	flatten apply(#c_0, s->(
	    u := c_1_s;
	--now focus on the maps starting from the u component of F_t
    	    numRComponents := #u-1;
    	    vv0 := mapComponents u; -- not all the vv0_i are valid.
	    (C,K) := componentsAndIndices F_(t-1);	    
	    vv := select(vv0, v-> member(v_3,K)); 
	  --for each member v of  vv, the list v_3 is the index of a component
	  --of F_(t-1) to which the u component maps.
	  --The rest of v describes the map, as follows:
    	    for v in vv list (
		sign := v_0;
		p := v_1;
		q := v_2;
		map(F_(t-1), F_t, 
		    (F_(t-1))_[u_{0..p-1}|{-1+sum u_{p..q}}|u_{q+1..numRComponents}]*
		    (if q<numRComponents 
		    then sign * (
	 		tensor (S, for i from 0 to p-1 list B_(u_i))**
	 		mA#(u_{p..q})**
	 		tensor(S, for i from q+1 to numRComponents-1 list B_(u_i))**
	 		G_(u_numRComponents)
			    	)
                    else sign * (
	     		tensor(S, for i from 0 to p-1 list B_(u_i))**
	     		mG#(u_{p..q})
			        )
		    )*
		    (F_t)^[u])
             ))))
    )

--We should probably break this into pieces, and have a function that produces
--the individual component corresponding to a member v of vv.


labeler = method()
--only direct sum modules can be labeled
labeler(Thing,Module) := (L,F) -> directSum(1:(L=>F));
--note that in labeling a direct sum, the labels must be applied to the modules
--And when the direct sum is formed.

label = method()
label(Module) := Thing => M-> (indices M)_0
label(List) := List => L-> apply(L, M ->(indices M)_0)

labeledDirectSum = method()
labeledDirectSum List := Module => L ->(
    --L is a list of labeled modules.
    ciL := apply(L, M -> componentsAndIndices M);
    directSum flatten apply(ciL, ci -> apply(#ci_0, i->(ci_1_i => ci_0_i)))
    )


///
restart
loadPackage"AInfinity"
check AInfinity
///

TEST///
S = ZZ/101[a,b]
C = labeledDirectSum({A,B},{S^1,S^2})
D = labeledDirectSum({X},{S^0})
--D = labeledDirectSum(S, {},{})
--D^[{}]
assert (componentsAndIndices C  == ({S^1, S^2}, {A,B}))
assert(componentsAndIndices C == ({S^1 , S^2 }, {A, B}))
assert(C^[A] == map(S^1,S^3,{{1,0,0}}))
assert(label components C == {A,B})
assert(indices C == {A,B})
///

///
--necessity of double labeling:
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

labeledTensorComplex = method()
labeledTensorComplex List := Complex => L -> (
    --Input is L = {C_0..C_(p-1)}, a list of Complexes. 
    --Returns the tensor product D of the C_i
    --with labels so that the tensor product of {(C_i)_(u_i)} is labeled u = {..u_i..}
    --ComponentsAndIndices applied to D_i gives the correct list of indices, and
    --thus picture D works; but ALSO D_i_[u] and D_i^[u] return the inclusion
    --and projection correctly. (Note that this requires "double" labeling.)
    
    if class L_0 =!= Complex then error"Input should be a list of Complexes.";
    S := ring L_0;
    if #L == 1 and class L_0 === Complex then (
	B := L_0;
	F := for i from min B to max B list labeler({i}, B_i);
	return complex(for i from min B to max B -1 list 
	        map(F_(i-min B),F_(i+1-min B), B.dd_(i+1)),
		Base => min B)
        );
    p := #L;
    Min := apply(L, C->min C);
    Max := apply(L, C->max C);
    modules := apply(#L + sum Max - sum Min, i ->(
	    d := i+sum Min;
	    com := select(compositions(p,d), c -> 
		    all(p, i->Min_i <= c_i and c_i<= Max_i) and c != {});
	    apply(com, co -> 
		    (co => labeler(co, 
			       tensor(S,apply(p, pp->(L_pp)_(co_pp))))))
	));
--note the (necessary) double labeling.
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
     (complex(d,Base => sum Min))
     )
	       
labeledTensorComplex Complex := Complex => C -> labeledTensorComplex{C}

labeledTensorComplex(Ring, Complex) := Complex => (R,C)->(
    --preserve the labels on C while tensoring each free module with R.
    --NOTE that C must be a labeled complex!
    
    c := for i from min C to max C list componentsAndIndices C_i;
    if c_(min C)_1_0 === null then error"Input Complex must be labeled";
    D := for j from 0 to max C - min C list if #c_j_0 === 1 then 
    --this is to fix the directSum bug
        labeler(c_j_1_0, R**c_j_0_0) else
    	directSum apply(#c_j_0, i -> labeler(c_j_1_i, R**c_j_0_i));
    complex (for i from 1 to max C - min C list map(D_(i-1),D_i,R**C.dd_(i+min C)), Base => min C)
    )
	


///
restart
loadPackage("AInfinity", Reload => true)
check AInfinity
///

TEST///
S = ZZ/101[a,b,c]
K' = complex koszul vars S

K = labeledTensorComplex K'
assert(label K_2 == {2})
assert(K_0_[{0}] == map(S^1,S^1,1))

K2 = labeledTensorComplex{K',K'}
picture K2
componentsAndIndices(K2_1)
assert(K2_1_[{1,0}] == map(S^{6:-1},S^{3:-1},id_(S^{3:-1})||0*id_(S^{3:-1})))

R = S/ideal a
RK = labeledTensorComplex(R,K)
picture RK
assert(label RK_2 == {2})
assert(RK_0_[{0}] == map(R^1,R^1,1))
///

///
restart
loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c,d]
R = S/(ideal(a,b,c,d))^2
elapsedTime H = aInfinity(R,3); 

K = toSequence (keys H)_{2..#keys H -1}
K = select(K, k-> class k === List)
for k in K do <<k<<" "<< picture H#k<<endl;

R = S/ideal apply(gens S, x->x^3)
use S

restart
loadPackage("AInfinity", Reload => true)
S = ZZ/101[a..e]
R = S/ideal"a3,b3,c3,d3,e3"
m = aInfinity(R,3)
B = m#"resolution"
--m{2,2} is skew-symmetric, mimicking A_1**A_1 -> A_2. and B2 commutes with B3.
map(B_4, B_3**B_2, m#{3,2}) ==map(B_4, B_2**B_3,m#{2,3}*tensorCommutativity (B_3,B_2))

///

aInfinity = method()
aInfinity (Ring,ZZ) := HashTable => (R,n) -> (
    --R should be a factor ring of a polynomial ring S
    --The HashTable returned contains the A-infinity structure on an
    --S-free resolution A of R up to m_n: B^(**n) --> B
    --CAVEAT: for the moment n = 3 is fixed! 
--old notation: m#{p,{u_1..u_p}}
--new notation: m#{u_1..u_p}. This is the map that has source
--B_(u_1)**..**B_(u_p), a p-factor tensor product.

m := new MutableHashTable;
m#"ring" = R;
S := ring presentation R;
RS := map(R,S);
A := freeResolution coker presentation R;
B := labeledTensorComplex complex(apply(length A-1, i -> -A.dd_(i+2)), Base =>2); -- new B!
m#"resolution" = B;

--m#{u_1}
apply(length B , i-> m#{i+3} = B.dd_(i+3));

--m#{u_1,u_2}
B2 := labeledTensorComplex{B,B};
A0 := complex {A_0};
d1 := map(A_0, B_2, A.dd_1);
d1d1 := hashTable for i from min B to max B list 
       i+2 => (d1**id_(B_i))*(B2_(i+2))^[{2,i}] - (id_(B_i)**d1)*(B2_(i+2))^[{i,2}];
D := map(A0**B,B2,d1d1, Degree => -2);
m0 := nullHomotopy D;
for i from 4 to 1+(concentration B)_1 do(
    (C,K) := componentsAndIndices B2_i;
    for k in K do (
	k' := {k_0+k_1-1};
	m#k = map(target (B_(i-1))^[k'], source (B2_i)_[k],
	       (B_(i-1))^[k']*m0_i*(B2_i)_[k]
	        )
	)
    );

--m#{u_1..u_3}	                    
B3 := labeledTensorComplex toList(3:B);
e := apply(3, ell -> toList(ell:0)|{1}|toList(3-ell-1:0));

for i from 3*2 to max B+1 do(
        co := select(compositions(3,i,max B), c -> min c >= min B);
	--(C,K) := componentsAndIndices (B2_i); is this better?
	for k in co do(
	dm3 := m#{sum k_{0,1}-1,k_2} * (m#(k_{0,1})**B_(k_2)) +
	
	       (-1)^(k_0)* m#{k_0,sum k_{1,2}-1} * (B_(k_0)**m#(k_{1,2})) +
        
	       sum(apply(3, ell -> if min(k-e_ell)< min B then 0 else (
			mm := tensor(S, apply(3, i-> if i == ell then m#(k_{ell}) else B_(k_i)));
		       (-1)^(sum k_{0..ell-1})*m#(k-e_ell)*mm)));
	       --mm is m#(k_{ell}) tensored with factors B_(k_i) in the appropriate order. eg, 
	       --if ell = 0,then
	       --mm = m#(k_{0})**B_(k_1)**B_(k_1)
	m3 := dm3//B.dd_(i-1);
        m#k = map(B_(i-1), B3_i, m3*B3_i^[k])
	)
     );
hashTable pairs  m
)

///
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "DGAlgebras"
kk = ZZ/101
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c))
mA = aInfinity(R,3)

assert isGolod R
M = coker vars R
E = burke(R,M,5)
E.dd^2 -- F_5-> F_4->F_3 is not 0. However, F_4 -> F_3 does surject onto ker F_3->F_2,
picture (E.dd_4 * E.dd_5)
picture E.dd_5
picture E.dd_4
extractBlocks(E.dd_4,{3,0},{4,0})*extractBlocks(E.dd_5,{4,0},{3,2,0})+
extractBlocks(E.dd_4,{3,0},{2,2,0})*extractBlocks(E.dd_5,{2,2,0},{3,2,0})

mA = aInfinity(R,3)
B = mA#"resolution"
A = freeResolution coker presentation R
B.dd
A.dd
A2=labeledTensorComplex{A,A}
B2=labeledTensorComplex{B,B}-- first half the same, not second!
B2' = dual B2
A2' = dual A2[2]
phi0' = map(A2'_(-8),B2'_(-8),1)
phi' = extend(A2',B2',phi0')
phi = dual phi'
P = map(B2,A2[-2],phi)

mul0= map(A_0,A2_0,1)
mul = extend(A,A2, mul0)

(C,K) = componentsAndIndices B2_5
(CA,KA) = componentsAndIndices A2_3
k = K_0
k' = apply(k, i->i-1)
A2_3_[k']

B2_5^[k]
ring A===ring B
phi = hashTable(apply(length A, i-> i=>if i >0 then map(A_i,B_(i+1),1) else map(A_0,B_0,0)))

///


///
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
    --m#{u} for #u = 1,2,3
    
m := new MutableHashTable;
m#"module" = M;
B := mR#"resolution";
R := ring M;
S := ring presentation R;
A := labeledTensorComplex freeResolution coker presentation R;
RS := map(R,S);

Mres := freeResolution pushForward(RS,M);
G := complex labeledTensorComplex{Mres};
m#"resolution" = G;

--m#u, #u=1
  apply(length G , i-> m#{i+1} = G.dd_(i+1));    

----m#u, #u=2
BG := labeledTensorComplex{B,G};
A0 := complex {A_0};
d1 := map(A_0, B_2, A.dd_1);
dG := hashTable for i from min G to max G list
              i+2 => (d1**id_(G_i))*(BG_(i+2))^[{2,i}];
D := map(A0**G, BG, dG, Degree => -2);
m0 := nullHomotopy D;
for i from 2 to 1+(concentration G)_1 do(
    (C,K) := componentsAndIndices BG_i;
    for k in K do (
	k' := {k_0+k_1-1};
	m#k = map(G_(i-1), source (BG_i)_[k],m0_i*(BG_i)_[k])
	)
    );

--m#u, #u=3	                       );
B2G := labeledTensorComplex (toList(2:B)|{G});
e := apply(3, ell -> toList(ell:0)|{1}|toList(3-ell-1:0));

for i from min B2G to max G+1 do(
	(C,K) := componentsAndIndices (B2G_i);
	for k in K do(
M := hashTable apply(e, ee-> 
           ee => tensor(S, apply(3, i-> (
		      if i<2    and ee_i == 0 then B_(k_i) else
		      if i == 2 and ee_i == 0 then G_(k_i) else
		      if m#?{k_i} then m#{k_i} else S^0))));
	  
	dm3 := -( m#{sum k_{0,1}-1,k_2} * (mR#(k_{0,1})**G_(k_2)) +
	
	       (-1)^(k_0) * m#{k_0,sum k_{1,2}-1} * (B_(k_0)**m#(k_{1,2})) +
	               
	       sum(apply(#e, ell ->
			if min(k-e_ell-{2,2,0})<0 then 0 else 
		       (-1)^(sum k_{0..ell-1}) * m#(k-e_ell) * M#{e_ell}))
		   );

	m3 := dm3//G.dd_(i-1);
        m#k = map(G_(i-1), source ((B2G_i)_[k]), m3))
     );
hashTable pairs  m)

///
restart
loadPackage("AInfinity", Reload => true)
kk = ZZ/101
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c)) -- a simple 3 variable Golod ring
K = koszul vars R
M = coker K.dd_2

mA = aInfinity(R,3)
B = mA#"resolution"
mG = aInfinity(mA,M,3)
G = mG#"resolution"

keys mG
mG#{2,2,0}
m#{sum k_{0,1}-1,k_2} * (mR#(k_{0,1})**G_(k_2)) +
1^(k_0) * m#{k_0,sum k_{1,2}-1} * (B_(k_0)**m#(k_{1,2})) 
m#{3,0}*(mR#{2,2}**G_0)

m#{2,1}*(B_2**m#{2,0})
m3 = dm3//G.dd_3
///
///
restart
debug loadPackage("AInfinity", Reload => true)
needsPackage "Complexes"
kk = ZZ/101
S = kk[x_1..x_3]
R = S/(x_1*ideal vars S)
R = S/((ideal vars S)^3)
R = S/ideal apply(gens S, x -> x^3)
RS = map(R,S)
M = coker vars R
elapsedTime mR = aInfinity(R,3)

G = (freeResolution pushForward(RS,M))
B = mR#"resolution"
BG = labeledTensorComplex{B,G}
p = new MutableHashTable from
for i from 2 to length G list i=>(presentation R ** G_(i-2))*(BG_i)^[{2,i-2}]
p#2
p#3
nullHomotopy map(G[-2],BG,p)
G[-2]
BG

for i from 2 to 4 list betti((G[-2])_i**presentation R)
map(G[-2],BG,i-> if G_i != 0 then (G[-2])_i**presentation R*(BG_i)^[{i,0}] else 0)
netList for i from 2 to 4 list (presentation R)*(BG_i)^[{2,i-2}]
for i from 0 to 3 list
((presentation R),(BG_(i+2))^[{2,i}])

componentsAndIndices (BG_i)
G

(G[-2])_i
(G[-2])_i**(presentation R * (BG_i)^[{i,0}])

componentsAndIndices(BG_i)
--this is from the  aInfinity(Ring,ZZ)
-*
d := map(A0, B, i-> if (i == 2) then A.dd_1 else 0);
m#"Bmap" = d;
BG := labeledTensorComplex{B,G};
for i from 2 to max BG list de_i*BG.dd_(i+1)+BG0.dd_(i)*de_(i)
*-
G0 = chainComplex complex G_0
BG0 = chainComplex labeledTensorComplex{B,G0}


concentration BG0
d = map(BG0, chainComplex BG, i-> if i<= 4 then ((BG_i)^[{i,0}])**presentation R else 0)
for i from 2 to 4 list betti( (BG_i)^[{i,0}]**presentation R)

(d_2//BG0.dd_3)*BG0.dd_3
m2 := map(S^1**G0, BG, i-> if i == 2 then presentation R ** G_0 else 0);

BG' := complex(for i from 2+min AG to max AG list AG.dd_i, Base => 2);
G' := complex(for i from 2 to max G list G.dd_i, Base => 1);
m0 := extend(G,AG,id_(G_0));
maps := hashTable for i from min G' to max G' list i+1=>map(G_i, BG'_(i+1), m0_i);





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

extractBlocks = method()
extractBlocks(Matrix, List) := Matrix => (phi, src) ->(
    -- returns the submatrix corresponding to the block or blocks listed in src.
    -- src is a list of integers or a list of such lists,
    -- respresenting block(s) in source phi.
    -- note that this behavior is DIFFERENT than the function with the same
    -- name in EagonResolution, where the list is an ordinal list of integers
    -- representing the blocks (in some order??).
    if class src_0 === ZZ then 
       srcList := {src} else srcList = src;
    phi1 := flattenBlocks phi;
    matrix {apply(srcList,Ls->
               phi1_[Ls])
	   }
    )


extractBlocks(Matrix, List, List) := Matrix => (phi, tar, src) ->(
    -- returns the submatrix corresponding to the block or blocks listed in src and tar.
    -- src and tar are lists of integers or lists of such lists,
    -- respresenting block(s) in phi.
    -- note that this behavior is DIFFERENT than the function with the same
    -- name in EagonResolution, where the list is an ordinal list of integers
    -- representing the blocks (in some order??).
    if class src_0 === ZZ then 
       srcList := {src} else srcList = src;
    if class tar_0 === ZZ then
       tarList := {tar} else tarList = tar;
    phi1 := flattenBlocks phi;
    matrix apply(tarList, Lt -> apply(srcList,Ls->
               phi1_[Ls]^[Lt])
	   )
    )
    
///
restart
loadPackage("AInfinity", Reload => true)
kk = ZZ/5
S = kk[a,b,c]
R = S/((ideal a^2)*ideal(a,b,c)) -- a simple 3 variable Golod ring
K = koszul vars R
M = coker K.dd_3
E = burke(R,M,5)
E.dd^2
apply(length E, i-> prune HH_(i)E)
E.dd_2
picture E.dd_2
displayBlocks E.dd_2
extractBlocks(E.dd_2,{1},{2,0})
picture extractBlocks(E.dd_2,{1},{{2},{2,0}})


displayBlocks E.dd_4
betti E.dd_4
///

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
trim ideal(m#{2,2,2})
----
restart
uninstallAllPackages()
installPackage"Complexes"
installPackage"FourTiTwo"
viewHelp Complexes

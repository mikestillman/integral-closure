newPackage(
        "EagonResolution",
        Version => "0.9", 
        Date => "September 1, 2020",
        Authors => {{Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => ""},
	      {Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"}},
        Headline => "Compute the Eagon Resolution of the residue field",
        DebuggingMode => true
        )


export {
    "eagon", 
--    "weight", currently not used
    "resolutionFromEagon", 
    "eBetti", -- total betti numbers from Eagon res
    "verticalStrand", --make a vertical strand of the Eagon complex
    "horizontalStrand", --make a vertical strand of the Eagon complex    
    "eagonSymbol", 
    "eagonSymbols",    
    "picture",
    "displayBlocks",
    "mapComponent"
    }

--SOME USEFUL INTERNAL FUNCTIONS
--    "isIsomorphic",
--    "isDegreeZeroSurjection",

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

verticalStrand = method()
verticalStrand (HashTable, ZZ) := ChainComplex =>  (E,n) -> (
    	   Kemax :=select(keys E, k -> (k_0 === "dVert" and E#k !=0));
           maxn := max apply(Kemax, k->k_1);
	   if n>maxn then error "That vertical strand wasn't defined";
    	   Ke := select(keys E, k -> (k_0 === 0 and k_1 === n and E#k !=0));
	   b := max (Ke/(k-> k_2));
           chainComplex(apply(b, i-> E#{"dVert", n,i+1})))
       
horizontalStrand = method()
horizontalStrand (HashTable, ZZ) := ChainComplex =>  (E,i) -> (
    	   Kemax :=select(keys E, k -> (k_0 === "dHor" and E#k !=0));
           maxi := max apply(Kemax, k->k_2);
	   if i>maxi then error "That horizontal strand wasn't defined";
    	   Ke := select(keys E, k -> (k_0 === 0 and k_2 === i and E#k !=0));
	   b := max (Ke/(k-> k_1));
           chainComplex(apply(b-1, n -> E#{"dHor", n+1,i})))
    
///
restart
loadPackage("EagonResolution", Reload => true)
///

TEST///
S = ZZ/101[a,b,c]
I = ideal(a,b)*ideal(a,b,c)
I = (ideal(a^2,b^3))^2
R = S/I
E = eagon(R,5);
assert(eBetti E == {1, 3, 6, 12, 24, 48})
V = verticalStrand(E,3)
V = horizontalStrand(E,2)
///

eBetti = method()
eBetti HashTable := List => E ->(
    K := keys E;
    K00 := sort select(K, k-> k_0 === 0 and k_2 === 0 and #k === 3);
    apply(K00, k-> rank E#k)
)

isDegreeZeroSurjection := method(Options => {Verbose => false})
isDegreeZeroSurjection(Module,Module) := o -> (A,B)->(
    --tests a random degree 0 map f:A --> B to see whether its a surjection, 
    --and returns the answer. If "true" and  o.Verbose == true then returns f.
    H := Hom(A,B);
    B0 := basis(0,H); -- this seems to be total degree 0 in case of degreeLength>1
    f := homomorphism(B0*random(source B0, (ring B0)^1));
    b := (coker f == 0);
    if (b and o.Verbose) then f else b
)

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

homologyCover = method()
homologyCover(ChainComplex,ZZ) := Matrix => (C,i) ->(
    --map from a free module to C_i giving a basis of HH_i C.
    --Note that HH_i C must be of finite length, or there's an error.
    B := basis HH_i C;
    (gens target B)*matrix B)

homologyCover(ZZ, ChainComplex) := List => (b,C) -> 
    apply(b, i-> homologyCover(C,i))

homologyCover(ChainComplex) := List => C -> homologyCover(1+length C, C)

homologyIsomorphism = method()
homologyIsomorphism(Module, ChainComplex, ZZ) := Matrix => (M,C,i) ->(
    --If M is isomorphic to HH_i C then the matrix returned is a map
    -- target presentation M --> C_i 
    --inducing the isomorphism.
    --else the function throws and error.
    Hi := HH_i C;
    H := prune Hi;
    p := H.cache.pruningMap; -- iso from H to HH_i C
    f := isDegreeZeroSurjection(M, H, Verbose => true);
    g := isDegreeZeroSurjection(H, M, Verbose => true); -- this is just a check; get rid of it eventually
    map(C_i,HH_i C, gens Hi)*p*f
)
///
restart
needsPackage "DGAlgebras"
debug loadPackage("EagonResolution", Reload =>true)

S = ZZ/101[a,b,c]
R = S/(ideal"ab,ac")^2 --a simple Golod ring on which to try this
b = 6
E = eagon(R,b);
F = resolutionFromEagon E
picture F.dd_4
isIsomorphic(X(1)**HH_0 Y1, HH_1 Y1)
///

labeler = (L,F) -> directSum(1:(L=>F));

trimWithLabel = method()
trimWithLabel ZZ := ZZ => n -> n

trimWithLabel Module := Module => M ->(
if M == 0 then return (ring M)^0;
ci := componentsAndIndices M;
pci := positions(ci_0,M -> M!=0);
if #pci ===0 then return (ring M)^0;
if #pci === 1 then labeler(ci_1_pci_0, ci_0_pci_0) else
            directSum apply(pci, i->labeler(ci_1_i,ci_0_i))
)

trimWithLabel Matrix := Matrix => f ->(
    S := source f;
    T := target f;
    S':= trimWithLabel S;
    T':= trimWithLabel T;
    map(T',T,id_T')*f*map(S,S',id_S)
    )

trimWithLabel HashTable := HashTable => E -> hashTable apply(keys E, k-> (k,trimWithLabel E#k))

trimWithLabel ChainComplex := ChainComplex => F -> chainComplex apply(
                              length F, i-> trimWithLabel(F.dd_(i+1))
			      )
    
eagon = method()
eagon(Ring, ZZ) := HashTable => (R,b) ->(
    --compute the Eagon configuration up to and including column b; and thus
    --also the "Eagon Resolution"
    --Y^b_0 \to...\to Y^1_0 \to Y^0_0. 

    --Let X_i be the free module R**H_i(K), where K is the Koszul complex on the variables of R.
        --We count X_i as having homological degree i+1.
    --The module Y^n_i = Eagon#{0,n,i} is described in Gulliksen-Levin as:
    --Y^0 = koszul vars R
    --Y^(n+1)_0 = Y^n_1; and 
    --for i>0, Y^(n+1)_i = Y^n_(i+1) ++ Y^n_0**X_i

    --Note that Y^n_i == 0 for i>1+length koszul vars R, so we will carry computations out to that length.

    --Each Y^n is a complex whose i-th homology is H_i(Y^n) = H_0(Y^n)^0**X_i (proved in Gulliksen-Levin).
    --assuming that the differential of Y^n and the maps Y^n --> Y^(n-1) are known
    --To construct the differential of Y^(n+1) and the map Y^(n+1) \to Y^n, 
    --this isomorphism must be made explicit.
    
    --The isomorphism is NOT given by a map of complexes from Y_i^0**K to Y_i --
    
    Eagon := new MutableHashTable;        

    g := numgens R;
    K0 := koszul vars R;
    Eagon#"numgens" = g;

    --now label the modules in the Koszul complex    
    K := chainComplex(for i from 1 to length K0 list 
	map(labeler((i-1,{}), K0_(i-1)),
	    labeler((i,{}), K0_(i)),
	    K0.dd_i));
    
    homologyCover' := (K,i) -> (
	--Returns the map from X(i) to K_i
        phi := homologyCover(K,i); 
        Xi := labeler((0,{i}),source phi); 
        map(K_i, Xi, phi)
        );
    
    ebasis := memoize homologyCover';
    X := i -> if i<=g and (s := source ebasis(K,i))!=0 then  
             labeler((0,{i}),s) else R^0; -- X(i) is the X_i of Gulliksen-Levin.
    --we made it a function so that it would be available for all integers i.
        pd := 0; while X(pd)!=0 do pd = pd+1; pd = pd-1; -- max i such that X(i)!=0
    	Eagon#"pd" = pd;
    
    --first make the free modules Y^n_i = Eagon#{0,n,i}. 
    --The maps Y^(n+1)_j \to Y^n_j will be Eagon#{"dHor",n+1,j}
    west := "dHor";
    --The differential verticaldiff of Y^n is the sum of maps eagon#{"dVert",n,i} and eagon#{"NW",n,i}.
    north := "dVert";
    beta := "beta";

    --Make the free modules Eagon#{0,n,i}. 
    --two special cases:
    for i from 0 to g+1 do (
	Eagon#{0,0,i} = K_i;-- print Eagon#{0,0,i}.cache.components);
      for n from 0 to b do(
           Eagon#{0,n,g+2} = directSum(1:R^0);-- R^0++R^0; 
       	                 ));
    -- cases:
    for n from 1 to b do (
    for i from 0 to g+1 do(	
       if i == 0 then (
	   Eagon#{0,n,i} = Eagon#{0,n-1,1} ;
	)
        else (
        Eagon#{0,n,i} = Eagon#{0,n-1,i+1}++eTensor(Eagon#{0,n-1,0},X(i));
	     )
    ));

    --Now make the northward maps; the maps of the complexes Y^n = E#{0,n,*}
    --Note that the highest term in Y^n is in place b-n, so the top interesting homology is H_(b-n-1)
    --initialize:
    for i from 0 to g+2 do Eagon#{north,0,i} = K.dd_i;
	       
--Make the maps for n=1:
    --three special cases:
    Eagon#{north, 1, g+2} = map(Eagon#{0,1,g+1}, Eagon#{0,1,g+2},0);
    Eagon#{west,1,0} = Eagon#{north, 0,1};

    Eagon#{north,1,1} = (Eagon#{north,0,2})*(Eagon#{0,1,1})^[0] +
	                    ebasis(K,1)*(Eagon#{0,1,1})^[1];
    Eagon#{beta,1,1} = ebasis(K,1);			    
    Eagon#{west,1,1} = K.dd_2 | ebasis(K,1);
    
    for i from 2 to g+1 do(
	Eagon#{north,1,i} = (Eagon#{0,1,i-1})_[0]*
	                    (
	                    (Eagon#{north,0,i+1})*(Eagon#{0,1,i})^[0] +
	                    ebasis(K,i)*(Eagon#{0,1,i})^[1]
			    );
        Eagon#{beta,1,i} = ebasis(K,i);			    
	Eagon#{west,1,i} = K.dd_(i+1) | ebasis(K,i);
			);
    		
--now the induction, assuming that the Y^m have been defined for m<n:
    for n from 2 to b do(
       Eagon#{north, n, g+2} = map(Eagon#{0,n,g+1}, Eagon#{0,n,g+2},0);
       Eagon#{west,n,0} = Eagon#{north, n-1,1};
       Eagon#{beta,n,0} = Eagon#{beta, n-1,1};       
    	    	    
    for i from 1 to g+1 do(
    	Eagon#{beta,n,i} = -((if #components Eagon#{0,n-2,i} ===1 then id_(Eagon#{0,n-2,i}) else
		                                                          Eagon#{0,n-2,i}_[0])*
                             Eagon#{beta,n-1,i}*
                               eTensor(Eagon#{north, n-2,1},X(i)) --,(a,b)->(a#0+b#0,a#1|b#1)) --*Eagon#{0,n,i}^[1]
		                   )//
			       Eagon#{north,n-2,i+1};
			               
	Eagon#{west,n,i} = Eagon#{0,n-1,i}_[0]*Eagon#{beta,n,i}*(Eagon#{0,n,i})^[1]+
	                   Eagon#{0,n-1,i}_[1]* (Eagon#{west,n-1,0}**X(i))  *(Eagon#{0,n,i})^[1]+
	                   (if Eagon#?{west,n-1,i+1} then 
			            Eagon#{0,n-1,i}_[0]*Eagon#{west,n-1,i+1}*Eagon#{0,n,i}^[0] 
				                     else 0);

	if i == 1 then Eagon#{north,n,i} = -- special case because Y^n_0 is not a tensor product with Y^(n-1)_0
	                    (
	                    (Eagon#{north,n-1,i+1})*((Eagon#{0,n,i})^[0])+
	                    Eagon#{0,n-1,i}_[0]*Eagon#{beta,n,i}*(Eagon#{0,n,i})^[1]+
			    Eagon#{0,n-1,i}_[1]*(Eagon#{north, n-2,1}**X(i))*(Eagon#{0,n,i}^[1])
			    )
		  else
	Eagon#{north,n,i} =
	    Eagon#{0,n,i-1}_[0]*
	                    (
	                    (Eagon#{north,n-1,i+1})*((Eagon#{0,n,i})^[0])+
	                    Eagon#{0,n-1,i}_[0]*Eagon#{beta,n,i}*(Eagon#{0,n,i})^[1]+
			    Eagon#{0,n-1,i}_[1]*(Eagon#{north, n-2,1}**X(i))*(Eagon#{0,n,i}^[1])
			    );
			));
trimWithLabel hashTable pairs Eagon
)

///
restart
loadPackage("EagonResolution", Reload=>true)
S = ZZ/101[a,b,c]/ideal(b^2,c^2) -- complete intersection
B = 6
E = eagon(S,B);
F = resolutionFromEagon(S,B)
F1 = resolutionFromEagon E
F2 = res (coker vars S, LengthLimit => 6)
///


resolutionFromEagon = method()
resolutionFromEagon(HashTable, ZZ) := ChainComplex => (E,b) ->(
    chainComplex(apply(b,n->E#{"dHor",n+1,0}))
    )

resolutionFromEagon HashTable := ChainComplex => E ->(
    b := max apply( select(keys E, k-> k_0 === 0 and k_2 === 0), k->k_1);
    resolutionFromEagon(E,b)
    )    

resolutionFromEagon(Ring,ZZ) := ChainComplex => (R,b) ->(
    resolutionFromEagon (eagon(R,b),b)
    )


///
restart
needsPackage "DGAlgebras"
debug loadPackage("EagonResolution", Reload =>true)
///

///
load"~/gitRepos/SocleInSyzygy/DaoSocle.m2"
S = ZZ/101[a,b]
ML = matrix"a,b2,0;
            0,b2,a"
isHomogeneous ML
MNL = matrix"a2,b2,0;0,a2,b2"
IL = minors(2, ML)
INL = minors(2,MNL)
isGolod(S/INL)
isGolod(S/IL)

kSS(S/IL, 5)
kSS(S/INL,5)
EL = eagon(RL=S/IL,6);

EL#{0,5,0};
netList pairs EL
ENL= eagon(S/INL,5);



EL#{0,1,3}
F6 = EL#{0,5,1}
(components F6)/components
FL = res coker vars (S/IL)
EL#{"dHor",3,0}
FL.dd_3
CL = chainComplex apply (4,i->EL#{"dHor",i+1,0})
prune HH_3 CL
FEL = resolutionFromEagon(S/IL,10)
apply(9, i-> prune HH_(i+1) FEL)

FNL = res coker vars(S/INL)
ENL#{"dHor",2,0}
FNL.dd_2
isIsomorphic(image FNL.dd_3, image ENL#{"dHor",3,0})
isDegreeZeroSurjection(image FNL.dd_2, image ENL#{"dHor",2,0})
--why isn't this being defined???: isDegreeZeroSurjection(image FNL.dd_2, image ENL#{"dHor",2,0},Verbose =>true)

betti FNL == betti G
G = resolutionFromEagon(S/INL, 6)
G.dd^2
apply(length G-1, i->prune HH_(i+1) G)

kk= ZZ/101
S = kk[x_0..x_3]
I = monomialCurveIdeal(S,{2,3,4})
R = S/I
E = eagon(R,6)
F = resolutionFromEagon(R,12)
betti (G = res(coker vars R, LengthLimit => 6))
F.dd_4
E#{"beta",4,0}
components source E#{"beta",3,1}
keys E
betti F
isGolod R
X1= R^1
X2 = R^2
X3 = R^3
X4= R^4

F = ("X1"=>X1)++("X2"=>X2)
G = ("X3"=>X3)++(C=>X4)
(components (F++F++G))/indices

indices oo
components oo
A = R^1++R^2, B= R^3++R^4

///


///
restart
loadPackage("EagonResolution", Reload=>true)
///

TEST/// -- test of eagon
needsPackage "DGAlgebras"
S = ZZ/101[a,b,c]
R = S/(ideal"ab,ac")^2 --a simple Golod ring on which to try this
assert(isGolod R)
bound = 6
E = eagon(R,bound);
Y = apply(bound, n-> chainComplex(apply(4, i-> E#{"dVert", n,i+1})));
assert(all(#Y, n->((Y_n).dd)^2 == 0))
assert all(#Y, n->isHomogeneous Y_n)
time F = resolutionFromEagon(R,bound)
time F' = res(coker vars R,LengthLimit => bound)
assert isHomogeneous F
assert all(bound-1,i-> prune HH_(i+1) F == 0)
assert(betti res(coker vars R,LengthLimit => bound) == betti F)

S = ZZ/101[a,b,c,d,e]
R = S/(ideal(e^2,d*e^4)+(ideal"ab,ac")^2) --a non-Golod ring, generators in different degrees
assert(not isGolod R)
E = eagon(R,10)
Y = apply(8, n-> chainComplex(apply(4, i-> E#{"dVert", n,i+1})));
isHomogeneous Y_0 -- this should be the koszul complex!!
assert(all(#Y, n->((Y_n).dd)^2 == 0))
assert all(#Y, n->isHomogeneous Y_n)
time F = resolutionFromEagon(R,8)
time F' = res(coker vars R,LengthLimit => 8)
assert isHomogeneous F
assert all(7,i-> prune HH_(i+1) F == 0)
betti F
betti F'

--the following lines don't quite do sensible things
apply(3, n->picture E#{"beta",n+1,2})
apply(3, n->displayBlocks E#{"beta",n+1,2})

///

--the following is almost right -- The indices of the X_i are not quite ok.
eagonSymbols = method()
eagonSymbols(ZZ,ZZ) := List => (n,i) ->(
    --symbol of the module Y^n_i, as a list of pairs, defined inductively from n-1,i+1 and n-1,0
    if n === 0 then return {(i,{})};
    if i === 0 then return eagonSymbols(n-1,1);
    e' := eagonSymbols (n-1,0);
    e'1 := apply (e', L ->prepend(i, L_1));
    eagonSymbols(n-1,i+1)|apply (#e', j-> (e'_j_0,e'1_j))
   )
-*
--the following code does not do what is claimed; and I don't think it's useful anyway!
eagonSymbols(ZZ,ZZ,ZZ) := List => (numv,pd,m) -> (
    --compute the list of all symbols of summands of the Y^n_i up to n = m, assuming a ring with numv variables
    --and projective dimension pd.
    maxK := numv;
    maxX := pd;
    result := flatten for i from 0 to maxK list (
        flatten for j from 1 to (m-i)//2 list (
            c := compositions(j, m-i-2*j, maxX-2);
            for c1 in c list prepend(i, (for a in c1 list a+2))
            )
        );
    if m <= maxK then result = append(result, {m});
    result)
*-

///
restart
loadPackage("EagonResolution", Reload=>true)
///

TEST///
eagonSymbols(1,2) == {(3, {}), (0, {2})}
assert (eagonSymbols(2,1) == eagonSymbols(3,0))
assert(eagonSymbols(1,3) == {(4, {}), (0, {3})})
assert(eagonSymbols(2,2) == {(4, {}), (0, {3}), (1, {2})})
assert(eagonSymbols(2,0) == {(2, {}), (0, {1})})
assert(eagonSymbols(3,1) == {(4, {}), (0, {3}), (1, {2}), (2, {1}), (0, {1, 1})})
///
    
///
restart
needsPackage "DGAlgebras"
loadPackage("EagonResolution", Reload =>true)

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
keys E
///


componentsAndIndices = (F) -> (
    if not F.cache.?components then (
        -- F has no components
        ({F}, {null})
        )
    else if #F.cache.components == 1 then (
        if F.cache.?indices then ({F}, F.cache.indices)
        else (F, {null})
        )
    else (
        a := for f in F.cache.components list componentsAndIndices f;
        (flatten(a/first), flatten(a/last))
        )
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
displayBlocks ChainComplex := List => C -> apply(length C, i -> displayBlocks(C.dd_(i+1)))
displayBlocks HashTable := List => E -> displayBlocks resolutionFromEagon E

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
picture ChainComplex := List => C -> apply(length C, i-> picture C.dd_(i+1))
picture HashTable := List => E ->  picture resolutionFromEagon E

mapComponent = method()
mapComponent(Matrix, Sequence, Sequence) := Matrix => (M,tar,src) -> (
    --Matrix should be one with labeled components, such as produced by
    --E = eagon(R,n)
    --M = E#{"dVert",4,1}
    --or
    --M = (resolutionFromEagon(R,n)).dd_4
    M1 := flattenBlocks M;
    --use "member" and "componentsAndIndices" to check reasonableness? or try evaluating and catch error.
    try (M2 := M1^[tar]_[src]) then M2 else 
    (<<endl<<"*** bad source or target symbol; use `picture M1' to check ***"<<endl<<endl; error())
    )

///
restart
loadPackage("EagonResolution", Reload => true)
S = ZZ/101[a,b,c,d,e]
R = S/(ideal(e^2,d*e^4)+(ideal"ab,ac")^2) --a non-Golod ring, generators in different degrees
E = eagon (R,6);
time F = resolutionFromEagon E
netList picture F
netList for n from 2 to 6 list picture E#{"beta",n,1}
mapComponent(E#{"dHor",3,0}, (0,{1}),(1,{1}))
picture E#{"dVert",3,1}
mapComponent(E#{"dVert",3,1}, (0,{2}),(0,{1,1})) 
picture E#{"beta",3,1}
mapComponent(E#{"beta",3,1}, (0,{2}),(0,{1,1})) 
mapComponent(E#{"beta",3,1}, (0,{3}),(0,{1,1})) 

///
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

beginDocumentation()

-*
restart
loadPackage "EagonResolution"
uninstallPackage "EagonResolution"
installPackage "EagonResolution"
viewHelp EagonResolution
*-

doc ///
Key
  EagonResolution
Headline
 Construct the double complex including the Eagon resolution of the residue field
Description
  Text
   Produces the components that make up a not-necessarily minimal resolution of
   the residue field of a ring R = S/I where S is a polynomial ring and I is an ideal.
   The resolution constructed is minimal if and only if R is Golod. The resolution
   constructed is called the Golod or Shamash or Eagon resolution, and the algorithm given here
   is the one by Jack Eagon. 
   
   The resolution could, perhaps more properly, be called the Golod-Eagon-Shamash
   resolution. It was described, in the special case where it is minimal, by
   E.S. Golod: Homology of some local rings, Uspekhi Mat. Nauk 33 (1978), no. 5(203), 177–178.
   A general construction was described by Jack Shamash:
   The Poincaré series of a local ring II, J. Algebra 17 (1971), 1–18
   and, perhaps around the same time, by Jack Eagon.
   Eagon's construction, superficially different than Shamash'
   was not published by him, but is described in Ch. 4 of the notes
   by Gulliksen and Levin: Homology of local rings,
   Queen's Paper in Pure and Applied Mathematics, No. 20 Queen's University, Kingston, Ont. 1969.  
   
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
      
   Eagon showed how this complex can be continued to a resolution.
   The underlying graded
   module of the complex is K ** T(F'), where F' is the complex F, shifted by
   1 in homological degree so that F_i is in homological degree i+1, and truncated
   by dropping F_0; and T(F') denotes the tensor algebra on the graded module F'.

   The differentials of this complex come from the differentials in the Koszul
   complex and various maps identifying the homology, at successive stages of the 
   construction, with tensor products of modules already constructed with the F_i.
   These are also the ingredients of
   the "Massey products" from topology, used by Golod to construct the complex
   in a special case.
   
   resolutionFromEagon produces the 
   (not necessarily minimal) resolution.  The functions picture and displayBlocks give
   alternate ways of viewing the innards of the resolution.
   
   The function @TO eagon @ produces a hashTable that contains all the data produced in
   Eagon's construction of the resolution: a double complex Y^n_i, and some internal 
   maps. The vertical differental is called dVert: Y^n_i -> Y^n_{i+1} and the horizontal
   differential is dHor: Y^n_i -> Y^{n-1}_i. 
   
  Example
   S = ZZ/101[a,b,c]
   I = ideal(a,b,c)*ideal(b,c)
   R = S/I
   E = eagon(R,5);
   F = resolutionFromEagon E
  Text
   As stated above, F = K\otimes T(F'), and one can see the maps between 
   each pair of summands. We denote the summand 
   K_i**F_{j_1}**..**F_{j_m} with the symbol (i,{j_1,..,j_m}), and we can write out
   the differentials in block form with the function displayBlocks:
  Example
   netList picture resolutionFromEagon(R,3)
  Text
   Since the matrices can be very large, it is sometimes better to know just whether
   a given block is zero or not, and this can be obtained with the function picture:
  Example   
   netList picture F
SeeAlso
   eagon
   resolutionFromEagon
   displayBlocks
   picture
///

doc ///
   Key
    resolutionFromEagon
    (resolutionFromEagon, Ring, ZZ)
   Headline
    computes a resolution of the residue field
   Usage
    F = resolutionFromEagon(R,n)
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
     resolutionFromEagon(R,5)
   SeeAlso
     EagonResolution
///


end--
-*
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
*-

-*
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
*-
-*
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
*-
-*
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
*-
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
    isEagonByShamash
    (isEagonByShamash,Ring)
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
     Tests whether resolutionFromEagon(R,1+numgens R)
     is minimal or not. It is a result of Avramov that it
     is enough to test this much of the resolution (Reason: all the Massey operations
     are already used in the first 1+numgens R maps.)
 
     It is known (Huneke- ***) that powers of ideals are Golod
    Example
     S = ZZ/101[a,b,c]
     R = S/(ideal vars S)^2
     res(coker vars R)
     resolutionFromEagon(R,4)
     assert(isGolodByShamash R == true)
    Text
     On the other hand, complete intersections are never Golod
    Example
     use S
     R = S/ideal"a3,b3,c3"
     res coker vars R
     F = resolutionFromEagon(R,4)
     F.dd_4
     assert(isGolodByShamash R == false)
   SeeAlso
    resolutionFromEagon
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


-*
restart
debug loadPackage("EagonResolution", Reload => true)
*-
TEST/// -- test of eagon
needsPackage "DGAlgebras"
S = ZZ/101[a,b,c]
R = S/(ideal"ab,ac")^2 --a simple Golod ring on which to try this
assert(isGolod R)
bound = 6
time F = resolutionFromEagon(R,bound)
netList picture F
E = eagon(R,bound);


netList picture F
netList for n from 2 to 6 list picture E#{"beta",n,1}
assert(F.dd^2 == 0)
assert isHomogeneous F
time F = resolutionFromEagon(R,bound)
time F' = res(coker vars R,LengthLimit => bound)
assert all(bound-1,i-> prune HH_(i+1) F == 0)
assert(betti res(coker vars R,LengthLimit => bound) == betti F)


S = ZZ/101[a,b,c,d,e]
R = S/(ideal(e^2,d*e^4)+(ideal"ab,ac")^2) --a non-Golod ring, generators in different degrees
assert(not isGolod R)
E = eagon (R,6)
E = eagon(R,8); -- without the ; it times out in conversion of output to net!
time F = resolutionFromEagon E
netList picture F
netList for n from 2 to 6 list picture E#{"beta",n,1}
M = flattenBlocks E#{"dHor",3,0}
mapComponent(M, (0,{2}),(0,{1,1})) -- bug  in mapComponent.

assert isHomogeneous F
assert (F.dd^2 == 0)
assert all(7,i-> prune HH_(i+1) F == 0)
///

end--


restart
uninstallPackage "EagonResolution"
restart
installPackage "EagonResolution"
viewHelp EagonResolution
check EagonResolution

restart


---- Mike ------------------------
-- labels are of the form
(2, {1,2,3}) -- refers to K_2 ** X_1 ** X_2 ** X_3

restart
debug needsPackage "EagonResolution"
R = QQ[a..d]
K0 = directSum(1:((0,{}) => R^1))
K1 = directSum(1:((1,{}) => R^{2,3,4,5}))
K2 = directSum(1:((2,{}) => R^{10,11,12,13,14,15}))
K3 = directSum(1:((3,{}) => R^{20,21,22,23}))
K4 = directSum(1:((4,{}) => R^{30}))

X1 = directSum(1:((0,{1}) => R^{100,101,102,103,104,105,106,107}))
X2 = directSum(1:((0,{2}) => R^{200,300,400,500,600}))
X3 = directSum(1:((0,{3}) => R^{300,301,302}))
X4 = directSum(1:((0,{4}) => R^{400,401}))

-- Consider one summand
assert(indices X1 == {(0, {1})})
assert(last componentsAndIndices X1 == indices X1)
assert(first componentsAndIndices X1 == components X1)
X1' = flattenBlocks X1
assert(componentsAndIndices X1' == componentsAndIndices X1)
assert(X1' == X1)

-- Consider 2 summands
F = X1 ++ X2
assert(indices F == {0,1})
assert(components F == {X1, X2})
assert(last componentsAndIndices F == {(0, {1}), (0, {2})})
assert(first componentsAndIndices F == {X1, X2})

F1 = flattenBlocks F
components F1
indices F1

F2 = flattenBlocks F1
assert(components F2 == components F1)
assert(indices F2 == indices F1)
assert((components F1)/indices == {{(0, {1})}, {(0, {2})}})

assert(components flattenBlocks F == {X1,X2})
assert(indices flattenBlocks F == {(0, {1}), (0, {2})})

-- Consider 3 summands
F = X1 ++ X2 ++ X3
assert(indices F == {0,1})
assert(components F == {X1++X2, X3})
assert(last componentsAndIndices F == {(0, {1}), (0, {2}), (0, {3})})
assert(first componentsAndIndices F == {X1, X2, X3})
F1 = flattenBlocks F
assert(last componentsAndIndices F1 == {X1,X2,X3}/indices//flatten)
assert(first componentsAndIndices F1 == {X1,X2,X3})
assert((first componentsAndIndices F1)/indices == {X1,X2,X3}/indices)

F2 = flattenBlocks F1
assert(componentsAndIndices F2 == componentsAndIndices F1)
indices F2
(components F2)/indices

-- Consider tensor products
G = tensorWithComponents(X1, X2, (a,b) -> (a#0+b#0, a#1|b#1))
assert(indices G == {(0, {1, 2})})
assert(components G == {G})
assert(indices first components G == indices G)
(components G)/indices

-- Matrices
m11 = map(X2, X3, 0)
m12 = map(X2, X4, 0) 
m21 = map(K2, X3, 0)    
m22 = map(K2, X4, 0)
m = matrix{{m11,m12},{m21,m22}}
m1 =flattenBlocks m
indices source m1
picture m
displayBlocks m

G = flattenBlocks(X3 ++ K2 ++ K3)
H = tensorWithComponents(G,X2, (a,b) -> (a#0+b#0, a#1|b#1))
indices H
componentsAndIndices X3
componentsAndIndices (X3 ++ K2)

(components F)/indices

--Irena's examples: m generic forms of degree d in n variables
restart
debug loadPackage("EagonResolution", Reload=> true)
--
(m,n,d) = (6,3,2)
S = ZZ/101[x_1..x_n]
I = ideal random(S^1,S^{m:-d})
R = S/I
E' = eagon(R,4);
E = resolutionFromEagon E'
res (coker vars R, LengthLimit=> 4)
E = resolutionFromEagon(R,n+1)
componentsAndIndices E'#{0,4,1}
componentsAndIndices E_4
displayBlocks (E.dd_4)
picture(M = E.dd_4)
mapComponent(M, (0,{2}), (0,{1,1}))


==================
picture E'#{"beta",4,0}
picture (M = E'#{"dHor",2,1})
displayBlocks (M = E'#{"beta",3,0})
indices source M
indices target M
M
--but these are ok:
displayBlocks E'#{"dHor",4,0}
picture E'#{"dHor",4,0}
keys E'
picture E'#{"dVert",3,1}
mapComponent(M, (0,{2}), (0,{1,1}))
mapComponent(M, (2,{}), (1,{1}))
picture M

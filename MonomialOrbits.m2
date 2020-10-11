newPackage(
        "MonomialOrbits",
        Version => "0.1", 
        Date => "8 Oct 2020",
        Authors => {{Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"},
	          {Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://pi.math.cornell.edu/~mike"}},
        Headline => "enumerate monomial ideals",
        DebuggingMode => true
        )

export {
--    "setupRing", -- eventually will be private?
--    "sumMonomials",
--    "normalForms",
    "orbitRepresentatives",
    "hilbertRepresentatives",
    "Group",
    "MonomialType"
--    "SquareFree"
    }

orbitRepresentatives = method(Options=>{Group=>"SymmetricGroup", MonomialType => "All"})
orbitRepresentatives(Ring, List) := List => o->(R, degs) -> (
    setupRing(R,degs,o); -- creates G and a list of lists of monomials in R.cache
    info := R.cache.MonomialOrbits;
    G := info#"GroupElements";
    result := {monomialIdeal 0_R};
    rawMonsMat := matrix{{}};
    mons := {};
      for d in degs do (
         rawMonsMat = if o.MonomialType === "All" then basis(d,R)
                     else if o.MonomialType === "SquareFree" then squareFree(d,R);
	 mons = flatten entries sort(rawMonsMat, 
		 DegreeOrder => Ascending, MonomialOrder => Descending);
         result = normalForms(sumMonomials(result, mons), G)
	     	     );
      result)

orbitRepresentatives(Ring, Sequence) := List => o->(R, degs) -> 
               orbitRepresentatives(R, toList degs)

hilbertRepresentatives = method(Options=>{Group=>"SymmetricGroup"})
hilbertRepresentatives(Ring, List) := List => o -> (R,h) -> (
    --orbit representatives of all monomial ideals I, if any, such that
    --hilbertFunction(i,R/I) = h_i for all i = 2,..,#h-2.
    setupRing(R,toList(2..#h-2));--,Group =>o#"Group"); -- creates G and a list of lists of monomials in R.cache
    G := R.cache.MonomialOrbits#"GroupElements";
    result := orbitRepresentatives(R, (hilbertFunction(2,R) - h_0):2);    

    scan(#h-1, i -> (
         rawMonsMat := basis(i+3,R);
	 mons := flatten entries sort(rawMonsMat, 
		 DegreeOrder => Ascending, MonomialOrder => Descending);
	     
        result = flatten for I in result list (
	defect := hilbertFunction(i+3, R/I) -  h_(i+1);

	if defect<0 then continue
	else (
	 result1 := {I};
	 scan(defect, j->(
         result1 = normalForms(sumMonomials(result1, mons), G);
 	     )
             ));
     	 result1);
             ));
    result)


setupRing = method(Options =>{Group => "SymmetricGroup", MonomialType => "all"})
--Group is either "SymmetricGroup" or a list of ring automorphisms
setupRing(Ring,List) := o -> (R,degs) -> (
    if not R.?cache then R.cache = new CacheTable;
    if not R.cache.?MonomialOrbits then R.cache.MonomialOrbits = new MutableHashTable;
    H := R.cache.MonomialOrbits;
    if H#?"MonomialType" then oldMonomialType := H#"MonomialType";
    
    if o.Group == "SymmetricGroup" then(
	    H#"Group" = "SymmetricGroup";
	    H#"GroupElements" = for p in permutations numgens R list
	       map(R,R,(vars R)_p))
    else (H#"GroupElements" = o.Group;
	      H#"Group" = "Other");
    )
-*	   
    if not H#?"monomials" then H#"monomials" = new MutableHashTable;
    for d in degs do
	if not H#"monomials"#?d then 
	   H#"monomials"#d = flatten entries sort(basis(d, R), 
		 DegreeOrder => Ascending, MonomialOrder => Descending);
*-

squareFree = method()
squareFree(ZZ, Ring) := Matrix => (d,R) -> (
    R' := coefficientRing R[gens R, SkewCommutative => true];
    substitute(basis(d,R'),R))
///
R = ZZ/101[x_0..x_5]
squareFree()
///

sumMonomials = method()
sumMonomials(List,List) := List => (L1,L2) -> (
  --L1 list of monomial ideals
  --L2 llist of monomials
  --return list of monomial ideals: an element of L1 
  --plus an element of L2 which is a minimal generator.
    unique flatten for I in L1 list (
	for m in L2 list (
	    if m % I != 0 then I + monomialIdeal m 
	    else continue))
    )
sumMonomials(Ideal,List) := List => (I,L2) -> sumMonomials({I}, L2)

normalForms = method()
normalForms(List, List) := (Fs, G) -> (
    -- Fs is a list of monomial ideals, G a group (list of ring maps)
    -- returns a subset of these that generate all, under the group G.
    G1 := drop(G,1);  -- remove the identity element.  ASSUMPTION: this is the first element!
    L := new MutableList from Fs;
    LH := hashTable for i from 0 to #Fs-1 list Fs#i => i;
    count := #L;
    for i from 0 to #L-1 list (
        if L#i === null then continue;
        F := L#i;
        --<< "F = " << F << endl;
        for f in G1 do (
            H := monomialIdeal(f F);
            if LH#?H then (
                j := LH#H;
                if j > i and L#j =!= null then (
                    L#j = null;
                    count = count - 1;
                    if count % 1000 == 0 then
                        << "  count: " << count << endl;
                    );
                );
            );
        F
        )
    )

///
restart
loadPackage("MonomialOrbits", Reload => true)
uninstallPackage "MonomialOrbits"
restart
installPackage "MonomialOrbits"
check "MonomialOrbits"
///

beginDocumentation()

doc ///
Key
  MonomialOrbits
Headline
 find orbit representatives of monomial ideals, specified by generator degrees or Hilbert function
///

TEST///
  R = ZZ/101[a,b]
  assert(hilbertRepresentatives(R,{2}) == {monomialIdeal a^2 , monomialIdeal(a*b)})
  assert(toString\hilbertRepresentatives(R,{2,1,0}) ==
    {"monomialIdeal(a^2,a*b^2,b^4)", "monomialIdeal(a^2,b^3)", "monomialIdeal(a^3,a*b,b^4)"})
  assert(hilbertRepresentatives(R,{2,3,0}) == {})

 R = ZZ/101[vars(0..3)]
 L = orbitRepresentatives(R,{2,2,2})
 assert(#L == 11)
  assert(#orbitRepresentatives(R,{2,3}) == 11)
--the following doesn't work, and I don't understand why!
-*
  R = ZZ/101[vars(0..5)]
 orbitRepresentatives(R,{4,5}, MonomialType => "SquareFree")
 {monomialIdeal (a*b*c*d, a*b*c*e*f)} -- gives an error
*-
///


end--

patterns = (S,deg,num) -> (
    n := numgens S;
    P := partitions(deg, n)/toList/sort;
    unique\\sort\toList\splice\(toList((set P)^**num))
)

pattern = m -> sort exponents m

///
netList patterns(S,3,2)
m = a^2*b
pattern m
///

monomialIdealsByPattern = method()
monomialIdealsByPattern (Ring, List) := List => (S,L) ->(
    --L should be a list of lists of non-negative integers, each of length numgens S, in rsort order.
    --Returns a list of monomial ideals in S generated by monomials whose exponent lists match L.
    if numgens S<#L then error"list is too long";
    M := orbit trim ideal apply(L, p-> product(#p, i-> S_i^(p_i)))
)


orbitRepresentatives = method(Options => {Strict => true})
orbitRepresentatives (Ring, List) := List => o -> (S,L) ->(
    --L should be a list of lists of non-negative integers, each of length numgens S, in rsort order.
    --Returns a list of orbit representatives of the 
    -- monomial ideals in S generated by monomials whose exponent lists match L.
    
    Lu := unique L;
    LL := apply(#Lu,i -> #select(L, ell -> ell == Lu_i));
    M := apply(#Lu, i -> monomialIdealsByPattern(S,{Lu_i}));
    MM = for i from 1 to #Lu -1 list ideal\subsets(M_i,LL_i);
    M_0)
-*
    I = {M_0_0};
    for j from 1 to #Lu-1 do(
    I = select(sum\ (I**M_j), J -> numgens trim J == j+1));
    I)
*-
    
///
restart
load "MonomialOrbits.m2"
S = ZZ/32003[x,y,z]
L = {{2,2,2}, {1,0,0}}
orbitRepresentatives(S,L)

L = {{3}}
monomialIdealsByPattern(S,{{3}})
L = {{3,0,0},{3,0,0}, {4,1,0}}



L = {{2,2,2}, {1,2,3}}
L = {{1,0,0},{2,0,0}}
P = patterns(S,3,2)

netList apply(P, p->orbitRepresentatives(S,p))


monomialIdealsByPattern (S,L)
I = ideal"x2y"
orbit I

///

orbit = I -> ( --orbit of a monomial ideal)
    S := ring I;
    n := numgens S;
    if not S#?"permutationMaps" then(
    maps  := apply(permutations n, q -> map(S,S,(vars S)_q));
    S#"permutationMaps" = maps
    );
    unique apply(S#"permutationMaps",f -> ideal rsort gens f I)
    )

end--
restart
load "MonomialOrbits.m2"

I = ideal"abc,c3"
I = ideal"ab,ac"

    
use S    


netList patterns(S,3,3)

unique\\sort\((partitions(deg, numgens S))/toList/sort ** (toList partitions(deg, numgens S))/toList/sort)

vars T
basis (2,T)

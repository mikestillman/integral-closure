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
    "setupRing", -- eventually will be private?
    "sumMonomials",
    "normalForms",
    "orbitRepresentatives",
    "Group"
    }

setupRing = method(Options =>{Group => "SymmetricGroup"})
--Group is either "SymmetricGroup" or a list of ring automorphisms
setupRing(Ring,List) := o -> (R,degs) -> (
    if not R.?cache then R.cache = new CacheTable;
    if not R.cache.?MonomialOrbits then R.cache.MonomialOrbits = new MutableHashTable;
    H := R.cache.MonomialOrbits;

    if o.Group == "SymmetricGroup" then(
	    H#"Group" = "SymmetricGroup";
	    H#"GroupElements" = for p in permutations numgens R list
	       map(R,R,(vars R)_p))
    else (H#"GroupElements" = o.Group;
	      H#"Group" = "Other");
	   
    if not H#?"monomials" then H#"monomials" = new MutableHashTable;
    for d in degs do
	if not H#"monomials"#?d then 
	   H#"monomials"#d = flatten entries sort(basis(d, R), 
		 DegreeOrder => Ascending, MonomialOrder => Descending);
    )

sumMonomials = method()
sumMonomials(List,List) := (L1,L2) -> (
  --L1 list of monomial ideals
  --L2 llist of monomials
  --return list of monomial ideals: an element of L1 
  --plus an element of L2 which is a minimal generator.
    unique flatten for I in L1 list (
	for m in L2 list (
	    if m % I != 0 then I + monomialIdeal m 
	    else continue))
    )

normalForms = method()
normalForms(List, List) := (Fs, G) -> (
    -- Fs is a list of monomial ideals, G a group (list of ring maps)
    -- G is a permutation group on these indices.
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


orbitRepresentatives = method(Options=>{Group=>"SymmetricGroup"})

orbitRepresentatives(Ring, List) := List => o->(R, degs) -> (
    setupRing(R,degs,o); -- creates G and a list of lists of monomials in R.cache
    info := R.cache.MonomialOrbits;
    G := info#"GroupElements";
    result := {monomialIdeal 0_R};
    for d in degs do result = normalForms(sumMonomials(result, info#"monomials"#d), G);
    result)

-*
orbitRepresentatives(List, List, List) := List => o->(Ls, L) -> normalForms(sumMonomials(Ls, L), o.Group)

orbitRepresentatives(List, ZZ, List) := List => o->(Ls, deg) -> (
    S := target first o.Group;
    setupRing(S,deg);
    L := S.cache.MonomialOrbits#deg#0;
    normalForms(sumMonomials(Ls, L), o.G)
    )
*-
beginDocumentation()

TEST ///
-*
  restart
  needsPackage "MonomialOrbits" 
*-
  S = ZZ/101[a,b,c,d]
  orbitRepresentatives(S,{2,3})
  setupRing(S,{2})
  setupRing(S,{2,3})

  setupRing(S,5)
  setupRing(S,2)
  assert(S.cache.MonomialOrbits#"perms" == permutations toList(0..numgens S - 1))
  M0 = {monomialIdeal(0_S)}
  M1 = addGenerator(M0, 2, G)
  M2 = addGenerator(M1, 2, G)
  M3 = addGenerator(M2, 2, G)
time  M4 = addGenerator(M3, 3, G)
time  M5 = addGenerator(M4, 3, G)
#M5

  M1 = addGenerators(M0, S.cache.MonomialOrbits#2#0, G)
  M1 = sumMonomials({monomialIdeal(0_S)}, S.cache.MonomialOrbits#2#0)
  M1 = normalForms(M1, G)
  M2 = sumMonomials(M1, S.cache.MonomialOrbits#2#0)
  M2 = normalForms(M2, G)
  M3 = sumMonomials(M2, S.cache.MonomialOrbits#3#0)
  M3 = normalForms(M3, G)
  G = for p in permutations {0,1,2} list map(S, S, (vars S)_p)
  M1 = sumMonomials({monomialIdeal(0_S)}, S.cache.MonomialOrbits#2#0)  
  for g in G list for m in M1 list g m;
///

end--

beginDocumentation()

doc ///
Key
  MonomialOrbits
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

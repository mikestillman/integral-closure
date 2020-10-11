newPackage(
        "MonomialOrbits",
        Version => "0.9", 
        Date => "10 Oct 2020",
        Authors => {{Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"},
	          {Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://pi.math.cornell.edu/~mike"}},
        Headline => "Orbit representatives of monomial ideals",
        DebuggingMode => false
        )

export {
    "orbitRepresentatives",
    "hilbertRepresentatives",
    "Group",
    "MonomialType"
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
         rawMonsMat = if o.MonomialType === "SquareFree" then squareFree(d,R)
	              else basis(d,R);
	 mons = flatten entries sort(rawMonsMat, 
		 DegreeOrder => Ascending, MonomialOrder => Descending);
         result = normalForms(sumMonomials(result, mons), G)
	     	     );
      result)

orbitRepresentatives(Ring, Sequence) := List => o->(R, degs) -> 
   orbitRepresentatives(R, toList degs, Group => o.Group, MonomialType => o.MonomialType)

hilbertRepresentatives = method(Options=>{Group=>"SymmetricGroup", MonomialType => "All"})
hilbertRepresentatives(Ring, List) := List => o -> (R,h) -> (
    --orbit representatives of all monomial ideals I, if any, such that
    --hilbertFunction(i,R/I) = h_i for all i = 2,..,#h-2.
    setupRing(R,toList(2..#h-2));--,Group =>o#"Group"); -- creates G and a list of lists of monomials in R.cache
    G := R.cache.MonomialOrbits#"GroupElements";
    result := if o.MonomialType == "SquareFree" then 
       orbitRepresentatives(R, (hilbertFunction(2,R) - h_0):2, MonomialType => "SquareFree") else
       orbitRepresentatives(R, (hilbertFunction(2,R) - h_0):2);	   
    rawMonsMat := matrix{{}};
    mons := {};
    
    scan(#h-1, i -> (
         rawMonsMat = if o.MonomialType === "All" then basis(i+3,R) else
                      if o.MonomialType === "SquareFree" then squareFree(i+3,R);
	 mons = flatten entries sort(rawMonsMat, 
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
hilbertRepresentatives(Ring, Sequence) := List => o->(R, degs) -> 
   hilbertRepresentatives(R, toList degs, Group => o.Group, MonomialType => o.MonomialType)


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

squareFree = method()
squareFree(ZZ, Ring) := Matrix => (d,R) -> (
    z := symbol z;
    R' := coefficientRing R[z_1..z_(numgens R), SkewCommutative => true];
    phi := map(R,R',vars R);
    phi basis(d,R'))
--    substitute(basis(d,R'),R))
///
R = ZZ/101[x_0..x_5]
squareFree(3,R)
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
viewHelp MonomialOrbits
///

beginDocumentation()

doc ///
Key
  MonomialOrbits
Headline
 find orbit representatives of monomial ideals under the symmetric group action
 on the variables of a polynomial ring. The set of monomials is specified by 
 generator degrees in @TO orbitRepresentatives @ or Hilbert function in @TO hilbertRepresentatives@.
 If the option MonomialType => "SquareFree" is given, then only square-free monomials are considered.
///

doc ///
   Key
    orbitRepresentatives
    (orbitRepresentatives, Ring, List)
    (orbitRepresentatives, Ring, Sequence)
    [orbitRepresentatives, Group]
    [orbitRepresentatives, MonomialType]    
   Headline
    find representatives of monomial ideals under variable permutation
   Usage
    L = orbitRepresentatives(R,degs)
   Inputs
    R:PolynomialRing
    degs:List 
     of degrees of generators
    degs:Sequence
     of degrees of generators
   Outputs
    L:List
     of monomial ideals
   Description
    Text
     The script creates the ring transformations defined by permuations of variables.
     If no Group is specified, uses the full symmetric group, but it is also possible
     to specify an arbitrary list of permutations. It then adds one generator at a time
     starting with the lowest degrees specified; after each addition it chooses
     representatives under the group action.
     
     If the option @TO MonomialType@ => "SquareFree" is set then only
     ideals of square-free monomials are considered.
    Example
     S = ZZ/101[a..d]
     L = orbitRepresentatives(S,(2,2,2))
     #L
     tally apply(L, m->betti res m)
     L' = orbitRepresentatives(S,(2,2,2), MonomialType => "SquareFree")
     #L'
     tally apply(L', m->betti res m)
    Text
     It is possible to specify non-existent types:
    Example
     S = ZZ/101[a,b]
     L = orbitRepresentatives(S,(2,2,2,2))
   SeeAlso
    hilbertRepresentatives
    Group
    MonomialType
///

doc ///
   Key
    hilbertRepresentatives
    (hilbertRepresentatives, Ring, List)
    (hilbertRepresentatives, Ring, Sequence)
    [hilbertRepresentatives, Group]
    [hilbertRepresentatives, MonomialType]    
   Headline
    find representatives of monomial ideals under variable permutation
   Usage
    L = hilbertRepresentatives(R,s)
   Inputs
    R:PolynomialRing
    s:List 
    s:Sequence
     of desired values of d->hilbertFunction(R/I,d) for d in (2..1+length s)
   Outputs
    L:List
     of monomial ideals
   Description
    Text
     The script creates the ring transformations defined by permuations of variables.
     If no Group is specified, uses the full symmetric group, but it is also possible
     to specify an arbitrary list of permutations. Starting with orbit representatives
     of monomial ideals generated
     by s_0 quadrics, it successively adds to each as many forms of degree d in (3..1+length s)
     as necessary to achieve the desired Hilbert function.
     After each addition it chooses
     representatives under the group action.
     
     If the option @TO MonomialType@ => "SquareFree" is set then only
     ideals of square-free monomials are considered.
    Example
     S = ZZ/101[a..d]
     L = hilbertRepresentatives(S,{7,10,13,16,19,22,25})
     apply(L, m-> hilbertPolynomial m)
     #L
     tally apply(L, m->betti res m)
     #unique apply(L, m->primaryDecomposition m)
     L = hilbertRepresentatives(S,{3},MonomialType =>"SquareFree")     
    Text
     It is possible to specify non-existent types:
    Example
     S = ZZ/101[a,b]
     L = hilbertRepresentatives(S,{4})
   SeeAlso
    orbitRepresentatives
    Group
    MonomialType
///

doc ///
   Key
    Group
   Headline
    Group => "SymmetricGroup" or {f_1..f_t}
   Description
    Text
     This option specifies a group of permutations of variables.
     Group => "SymmetricGroup" or Group => GG, 
     where GG is a list of permutations of the variables as maps S -> S.
     The default, "SymmetricGroup" uses the full symmetric group.
///
doc ///
   Key
    MonomialType
   Headline
    MonomialType => "SquareFree" or "All"
   Usage
    orbitRepresentatives(S,degs,MonomialType => "SquareFree")
   Description
    Text
     The default is "All" (anything other than "SquareFree" is equivalent to "All").
///

///
uninstallPackage "MonomialOrbits"
restart
installPackage "MonomialOrbits"
viewHelp MonomialOrbits
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
  R = ZZ/101[vars(0..5)]
 orbitRepresentatives(R,{4,5}, MonomialType => "SquareFree") == {monomialIdeal (a*b*c*d, a*b*c*e*f)}
///


end--


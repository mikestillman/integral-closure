newPackage(
    "MonomialOrbits",
    Version => "0.9", 
    Date => "12 December 2020",
    Authors => {{Name => "David Eisenbud", 
            Email => "de@msri.org", 
            HomePage => "http://www.msri.org/~de"},
        {Name => "Mike Stillman", 
            Email => "mike@math.cornell.edu", 
            HomePage => "http://pi.math.cornell.edu/~mike"}},
    Headline => "Orbit representatives of monomial ideals",
    PackageExports =>{"Truncations"}, -- for 'truncate'
    DebuggingMode => true
    )

export {
    "orbitRepresentatives",
    "hilbertRepresentatives",
    "Group",
    "MonomialType"
    }

squareFree = method()
squareFree(List, Ring) := Matrix => (d,R) -> (
    if degreeLength R != #d then 
        error("expected degrees of length "|degreeLength R);
    z := symbol z;
    R' := coefficientRing R[z_1..z_(numgens R), SkewCommutative => true, Degrees => degrees R];
    phi := map(R,R',vars R);
    phi basis(d,R')
    )
squareFree(ZZ, Ring) := Matrix => (d,R) -> squareFree({d}, R)

///
  R = ZZ/101[x_0..x_5]
  squareFree(3,R)
///

monomialsInDegree = (d, R, type) -> (
    -- d: integer, or list (multidegree).
    -- R: polynomial ring
    -- type is either "All", "SquareFree" (anything else is an error)
    -- return: is a matrix of monomials of the given type and degree
    if type === "SquareFree" then 
        squareFree(d, R)
    else if type === "All" then 
        basis(d, R)
    else 
        error "expected MonomialType to be either \"All\" or \"SquareFree\""
    )
orbitRepresentatives = method(Options=>{Group=>"SymmetricGroup", MonomialType => "All"})

orbitRepresentatives(Ring, VisibleList) := List => o -> (R, degs) -> (
    setupRing(R,o); -- creates G as a list of ring automorphisms
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
    result
    )

orbitRepresentatives(Ring, MonomialIdeal, VisibleList) := List => o -> (R, I, degs) -> (
    setupRing(R, o); -- creates G and a list of lists of monomials in R.cache
    info := R.cache.MonomialOrbits;
    G := info#"GroupElements";
    result := {I};
    rawMonsMat := matrix{{}};
    mons := {};
    for d in degs do (
        rawMonsMat = monomialsInDegree(d, R, o.MonomialType);
        mons = flatten entries sort(rawMonsMat, 
                     DegreeOrder => Ascending, MonomialOrder => Descending);
        result = normalForms(sumMonomials(result, mons), G)
        );
    result
    )

///
  restart
  debug loadPackage("MonomialOrbits", Reload => true)
///

--orbitRepresentatives(Ring, Sequence) := List => o->(R, degs) -> 
--   orbitRepresentatives(R, toList degs, Group => o.Group, MonomialType => o.MonomialType)

hilbertRepresentatives = method(Options=>{Group=>"SymmetricGroup", MonomialType => "All"})
hilbertRepresentatives(Ring, VisibleList) := List => o -> (R, h) -> (
    --orbit representatives of all monomial ideals I, if any, such that
    --hilbertFunction(i,R/I) = h_(i-1) for all i = 1,..,#h.
    setupRing(R, o); -- creates G and a list of lists of monomials in R.cache
    G := R.cache.MonomialOrbits#"GroupElements";
    
    if h_0 > numgens R then error "not enough variables";
    if min h < numgens R and o.MonomialType == "SquareFree" then return {};
    
    result := if h_0 == numgens R then 
                  {monomialIdeal 0_R} 
              else
                  {monomialIdeal((gens R)_{0..numgens R - h_0 -1})};
    rawMonsMat := matrix{{}};
    mons := {};
    for i from 2 to #h do (
        rawMonsMat = monomialsInDegree(i, R, o.MonomialType);
        mons = flatten entries sort(rawMonsMat,
                     DegreeOrder => Ascending, MonomialOrder => Descending);
        result = flatten for I in result list (
            mons = flatten entries sort(compress(rawMonsMat % truncate(i, I)),
                DegreeOrder => Ascending, MonomialOrder => Descending);
            defect := hilbertFunction(i, R^1/I) -  h_(i-1);
            if defect < 0 then continue;
            if h_(i-1) == 0  then (
                if mons == {} then result1 := {I}
                else result1 = {monomialIdeal trim (I+ideal mons)}
                )
            else (
                result1 = {I};
                scan(defect, j->(
                        result1 = normalForms(sumMonomials(result1, mons), G);
                        ))
                );
     	    result1);
        );
    result
    )

///
  restart
  debug loadPackage("MonomialOrbits", Reload => true)
///


setupRing = method(Options => {Group => "SymmetricGroup", MonomialType => "all"})
--Group is either "SymmetricGroup" or a list of ring automorphisms
setupRing Ring := o -> R -> (
    if not R.?cache then R.cache = new CacheTable;
    if not R.cache.?MonomialOrbits then R.cache.MonomialOrbits = new MutableHashTable;
    H := R.cache.MonomialOrbits;
    if H#?"MonomialType" then oldMonomialType := H#"MonomialType";
    
    if o.Group == "SymmetricGroup" then (
        H#"Group" = "SymmetricGroup";
        H#"GroupElements" = for p in permutations numgens R list
            map(R, R, (vars R)_p)
        )
    else (
        H#"GroupElements" = o.Group;
        H#"Group" = "Other");
    )


sumMonomials = method(Options => {Group => "SymmetricGroup"})
sumMonomials(List, List) := List => o -> (L1, L2) -> (
    --L1 list of monomial ideals
    --L2 llist of monomials
    --return list of monomial ideals: an element of L1 
    --plus an element of L2 which is a minimal generator.
    unique flatten for I in L1 list (
        for m in L2 list (
            if m % I != 0 then I + monomialIdeal m 
            else continue
            )
        )
    )
sumMonomials(Ideal, List) := List => (I, L2) -> sumMonomials({I}, L2)

normalForms = method()
normalForms(List, List) := (Fs, G) -> (
    -- Fs is a list of MonomialIdeal s, G a list of ring maps
    -- returns a subset of these that generate all, under the action of G.
    -- G should be the set of coset representatives (beginning with the identity
    -- of the stabilizer of the ideal already found.
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
                    if count % 1000 == 0 and debugLevel > 0 then
                        << "  count: " << count << endl;
                    );
                );
            );
        F
        )
    )

stabilizer = method()
stabilizer(List, Ideal) := List => (G, I) -> (
    --  I and ideal in S
    --  G is a list of automorphisms S->S
    --  ouput is a list of those maps in G that fix I
    select(G, f-> gens f I % I == 0)
    )

cosets = method()
cosets(List, List) := List => (G, H) -> (
    H' := set H;
    G' := set G;
    representatives := {G_0}; -- should be the identity of G
    while G' - H' =!= set{} do (
        g := (toList(G'-H'))_0;
        representatives = append(representatives, g);
        H' = H' + set for h in H list g*h;
        );
    representatives
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
    Description
        Text
            This package contains functions for the construction of
            monomial ideals, generated by a certain number of elements
            of each degree, or given by a Hilbert function, up to the
            action of the symmetric group permuting the variables of a
            polynomial ring.
            
            The set of
            monomials is specified by generator degrees in @TO
            orbitRepresentatives @ or Hilbert function in @TO
            hilbertRepresentatives@.  If the option {\tt MonomialType =>
            "SquareFree"} is given, then only square-free monomials are
            considered.
            
            If the option {\tt Group => {...}} is given, (as a list of ring maps generating
            a subgroup of the symmetric group, then monomial ideals up to equivalence via
            this group are generated.
///

doc ///
    Key
        orbitRepresentatives
        (orbitRepresentatives, Ring, VisibleList)
        (orbitRepresentatives, Ring, MonomialIdeal, VisibleList)
        [orbitRepresentatives, Group]
        [orbitRepresentatives, MonomialType]    
    Headline
        find representatives of monomial ideals under variable permutation
    Usage
        L = orbitRepresentatives(R, degs)
        L = orbitRepresentatives(R, I, degs)
    Inputs
        R:PolynomialRing
        degs:List 
            or @ofClass Sequence@, of the degrees of the generators
        I:Ideal
            starting ideal.  All generated ideals will contain this one
        Group => List
            or @ofClass Symbol@.  If not given, or is {\it SymmetricGroup}, 
            the symmetric group of permutations on
            the variables of $R$ is used.  If a list is given, it
            should be a list of ring maps, each corresponding to a
            permutation of the variables, and should contain all of
            the elements of the desired group of permutations
        MonomialType => String
            Allowed values are {\tt "All"}, in which case all monomials are
            considered, and {\tt "SquareFree"},
            in which case only square free monomials are considered
    Outputs
        L:List
            of monomial ideals
    Description
        Text
            This method generates a list of representative ideals
            (under the group of permutations of the variables) generated by
            monomials and having generators in the specified degrees.

            If the option @TO MonomialType@ is set to "SquareFree",
            then only ideals of square-free monomials are considered.

            If no {\tt Group} is specified, the full symmetric
            group is used, but it is also possible to specify an arbitrary
            list of permutations. 
            
            This function adds one generator at a time
            starting with the first degree specified; after each
            addition it chooses representatives under the group
            action.  Two ideals are considered equivalent if one is
            the image under another via one of the given ring maps (so
            it is best to make sure they generate the entire group you
            are interested in).
     
            Note that {\tt degs} is specified as a VisibleList, which could
            be either a list or a sequence.
        Example
            S = ZZ/101[a..d]
            L = orbitRepresentatives(S,(2,2,2))
            #L
            tally apply(L, m->betti res m)
            L' = orbitRepresentatives(S,(2,2,2), MonomialType => "SquareFree")
            #L'
            tally apply(L', m->betti res m)
            I = monomialIdeal"a2,b2,c2,d2"
            L'' = orbitRepresentatives(S,I,{2,2,2})
            tally apply(L'', m->betti res m)
        Text
            It is possible to specify data which results in no ideals:
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
        (hilbertRepresentatives, Ring, VisibleList)
        [hilbertRepresentatives, Group]
        [hilbertRepresentatives, MonomialType]    
    Headline
        find representatives of monomial ideals under variable permutation
    Usage
        L = hilbertRepresentatives(R,s)
    Inputs
        R:PolynomialRing
        s:VisibleList 
            of desired values of {\tt d->hilbertFunction(R/I,d)} for d in (1..length s)
        Group => List
            or @ofClass Symbol@.  If not given, or is {\it SymmetricGroup}, 
            the symmetric group of permutations on
            the variables of $R$ is used.  If a list is given, it
            should be a list of ring maps, each corresponding to a
            permutation of the variables, and should contain all of
            the elements of the desired group of permutations
        MonomialType => String
            Allowed values are {\tt "All"}, in which case all monomials are
            considered, and {\tt "SquareFree"},
            in which case only square free monomials are considered
    Outputs
        L:List
            of monomial ideals
    Description
        Text
            This method generates a list of representative ideals
            (under the group of permutations of the variables) generated by
            monomials and having the given Hilbert function in the given degree range.

            If the option @TO MonomialType@ is set to "SquareFree",
            then only ideals of square-free monomials are considered.

            If no {\tt Group} is specified, the full symmetric
            group is used, but it is also possible to specify an arbitrary
            list of permutations. 

            Starting with orbit representatives of monomial ideals
            generated by all but s_0 linear forms, it successively adds to each as
            many forms of degree d in (2..1+length s) as necessary to
            achieve the desired Hilbert function.  After each addition
            it chooses representatives under the group action.

            Note that the (partial) Hilbert function is specified as a
            @TO VisibleList@, which could be either a list or a sequence.
        Example
            S = ZZ/101[a..d]
            L = hilbertRepresentatives(S,{4,4,1,0})
            #L
            L = hilbertRepresentatives(S,(4,7,10,13,16)); 
            #L
            L0 = hilbertRepresentatives(S,{4,7,10,13,16,0}); -- with a 1 instead of a 0 this is too slow
            #L0
            LP = apply(L, m-> hilbertPolynomial m)
            #LP
            #unique LP
            tally apply(L, m->betti res m)
            #unique apply(L, m->primaryDecomposition m)
            L = hilbertRepresentatives(S,{4,7},MonomialType =>"SquareFree")     
        Text
            It is possible to specify data which results in no ideals:
        Example
            S = ZZ/101[a,b]
            hilbertRepresentatives(S,{1,4}) == {}
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
            This option specifies a group of permutations of
            variables.  Group => "SymmetricGroup" or Group => GG,
            where GG is a list of permutations of the variables as
            maps S -> S.  The default, "SymmetricGroup" uses the full
            symmetric group.
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


TEST///
  S = ZZ/101[a,b,c]
  I = monomialIdeal"a3,b3,c3"
  assert(#orbitRepresentatives(S,{3,3,3}) == 25)
  assert(#orbitRepresentatives(S,I,{3}) == 2)

  R = ZZ/101[a..f]
  assert(
      orbitRepresentatives(R,{4,5}, MonomialType => "SquareFree") 
      == {monomialIdeal (a*b*c*d, a*b*c*e*f)})
///    

TEST///
  R = ZZ/101[a,b]
  assert(hilbertRepresentatives(R,{2,2}) == {monomialIdeal a^2 , monomialIdeal(a*b)})
  assert(toString\hilbertRepresentatives(R,{2,2,1,0}) =={"monomialIdeal(a^2,a*b^2,b^4)", "monomialIdeal(a^2,b^3)", "monomialIdeal(a^3,a*b,b^4)"})
  assert(hilbertRepresentatives(R,{2,3,0}) =={monomialIdeal(a^3,a^2*b,a*b^2,b^3)})

  R = ZZ/101[a,b,c]
  assert(#hilbertRepresentatives(R,{2}) == 1)
  assert(#hilbertRepresentatives(R,{2,0}) == 1)

  assert(#hilbertRepresentatives(R,{2,2,1})  == 3)
  assert(#hilbertRepresentatives(R,{2,2,1,0}) == #hilbertRepresentatives(R,{2,2,1}))

  assert(#hilbertRepresentatives(R,{3,4,5}) == 2)
  assert(#hilbertRepresentatives(R,{3,4,0}) == 4)
///

TEST///
  debug needsPackage "MonomialOrbits"
  S = ZZ/101[a,b,c,d]
  setupRing S	
  assert(#S.cache.MonomialOrbits#"GroupElements" == 24)
  G = S.cache.MonomialOrbits#"GroupElements"
  H = {G_0,G_1}
  C = cosets(G,H)
  assert(#C == 12)
  assert(24 ==#unique flatten for h in H list for c in C list (c*h))
///

end--

uninstallPackage "MonomialOrbits"
restart
installPackage "MonomialOrbits"
check "MonomialOrbits"
viewHelp MonomialOrbits

///
  restart
  needsPackage "MonomialOrbits"
  S = ZZ/101[a,b,c,d,e,f]
  I = minors(2, genericSymmetricMatrix(S, a, 3))
  for i from 0 to 6 list hilbertFunction(i, comodule I)
  -- {1, 6, 15, 28, 45, 66, 91}
  hilbertRepresentatives(S, {6, 15, 28, 45, 66}, MonomialType => "SquareFree");
  squareFree(3,S)
  
  debug needsPackage "MonomialOrbits"  
  S = ZZ/101[a,b,c,d,e,f]
  monomialsInDegree(3, S, "All")
  monomialsInDegree(3, S, "SquareFree")

  debug needsPackage "MonomialOrbits"  
  S = ZZ/101[a,b,c,d,e,f, Degrees => {3:{0,1},3:{1,0}}]
  monomialsInDegree({1,3}, S, "All")
  monomialsInDegree({1,3}, S, "SquareFree")
///

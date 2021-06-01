newPackage(
    "MonomialOrbits",
    Version => "1.0", 
    Date => "18 December 2020, rev 30 May 2021",
    Authors => {{Name => "David Eisenbud", 
            Email => "de@msri.org", 
            HomePage => "http://www.msri.org/~de"},
                {Name => "Mike Stillman", 
            Email => "mike@math.cornell.edu", 
            HomePage => "http://pi.math.cornell.edu/~mike"}},
    Headline => "Orbit representatives of monomial ideals",
    Keywords => {"Combinatorial Commutative Algebra"},
    PackageExports =>{"Truncations"}, -- for 'truncate'
    DebuggingMode => false
    )
-*
newPackage(
    "MonomialOrbits",
    Version => "1.0", 
    Date => "18 December 2020, rev 7 May 2021",
    Authors => {{Name => "David Eisenbud", 
            Email => "de@msri.org", 
            HomePage => "http://www.msri.org/~de"},
        {Name => "Mike Stillman", 
            Email => "mike@math.cornell.edu", 
            HomePage => "http://pi.math.cornell.edu/~mike"}},

    Keywords => {"Combinatorial Commutative Algebra"},
    PackageImports =>{"Truncations"}, -- for 'truncate'
    DebuggingMode => true
    )
*-

export {
    "orbitRepresentatives",    
    "hilbertRepresentatives",
    --options
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


monomialsInDegree = method()
monomialsInDegree(ZZ, Ring, String) := Matrix => (d, R, type) -> monomialsInDegree({d}, R, type)
monomialsInDegree(List, Ring, String) := Matrix => (d, R, type) -> (
    -- d: integer, or list (multidegree).
    -- R: polynomial ring
    -- type is either "All", "SquareFree" (anything else is an error)
    -- return: is a matrix of monomials of the given type and degree
    if #d != degreeLength R then error"expected valid (multi)degree";
    if type === "SquareFree" then 
        squareFree(d, R)
    else if type === "All" then 
        basis(d, R)
    else 
        error "expected MonomialType to be either \"All\" or \"SquareFree\""
    )

-*
oldOrbitRepresentatives = method(Options=>{MonomialType => "All"})

oldOrbitRepresentatives(Ring, VisibleList) := List => o -> (R, degs) -> (
    oldOrbitRepresentatives(R, monomialIdeal 0_R, degs, o))

oldOrbitRepresentatives(Ring, Ideal, VisibleList) := List => o -> (R, I, degs) -> (

    if not isMonomialIdeal I then error"oldOrbitRepresentatives:arg 1 is not a monomial ideal";
    result := {monomialIdeal I};

    G := permutations R;
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


--TODO
oldOrbitRepresentatives(Ring, Ideal, Ideal, ZZ) := List => o -> (R, I, startmons, numelts) -> (
         
    --take or subtract numelts elements from startmons mod I, plus I.

    if not isMonomialIdeal I then error"oldOrbitRepresentatives:arg 1 is not a monomial ideal";
    I = monomialIdeal I;

    if not isMonomialIdeal startmons then error"oldOrbitRepresentatives:arg 2 is not a monomial ideal";
    startmons = monomialIdeal startmons;

    G := permutations R;
    start := compress ((gens startmons) % I);

    if numelts < 0 then(
	    L := flatten entries start;
    	    sL := subsets(L, #L+numelts)/monomialIdeal;
    	    return normalForms(apply(sL, ell -> ell + I), G)
    ) else

    result := {I};
    mons := flatten entries sort(start,
                    DegreeOrder => Ascending, MonomialOrder => Descending);

    apply(numelts, i-> (
	<<"----"<<endl;	    
	elapsedTime sums := sumMonomials(result, mons);
        elapsedTime result = normalForms(sums, G)
        ));
    result
    )

--this version is slightly SLOWER.
oldOrbitRepresentatives1 = method(Options => {MonomialType => "All"})
oldOrbitRepresentatives1(Ring, Ideal, Ideal, ZZ) := List => o -> (R, I, startmons, numelts) -> (
         
    --take or subtract numelts elements from startmons mod I, plus I.

    if not isMonomialIdeal I then error"oldOrbitRepresentatives:arg 1 is not a monomial ideal";
    I = monomialIdeal I;

    if not isMonomialIdeal startmons then error"oldOrbitRepresentatives:arg 2 is not a monomial ideal";
    startmons = monomialIdeal startmons;

    G := permutations R;
    start := compress ((gens startmons) % I);

    if numelts < 0 then (
<<"subtracting"<<endl;
	result0 :=oldOrbitRepresentatives1(R, I, startmons, -numelts);
	result1 := apply(result0, J -> monomialIdeal(gens J % I));
	result := apply(result0, K -> I+ monomialIdeal(gens startmons %K));
	) else
    	
    result = {I};
    mons := flatten entries sort(start,
                    DegreeOrder => Ascending, MonomialOrder => Descending);

    apply(numelts, i-> (
	<<"----"<<endl;	    
	elapsedTime sums := sumMonomials(result, mons);
        elapsedTime result = normalForms(sums, G)
        ));
    result
    )
*-

hilbertRepresentatives = method(Options=>{MonomialType => "All"})
hilbertRepresentatives(Ring, VisibleList) := List => o -> (R, h) -> (
    --orbit representatives of all monomial ideals I, if any, such that
    --hilbertFunction(i,R/I) = h_(i-1) for all i = 1,..,#h.
    G := permutations R;
    
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

permutations Ring := R -> (
    if not R.?cache then R.cache = new CacheTable;
    if not R.cache.?MonomialOrbits then R.cache.MonomialOrbits = new MutableHashTable;
    H := R.cache.MonomialOrbits;
    if not H#?"GroupElements" then
        H#"GroupElements" = for p in permutations numgens R list
            map(R, R, (vars R)_p);
    H#"GroupElements"
    )

sumMonomials = method()
sumMonomials(List, List) := List => (L1, L2) -> (
    --L1 list of monomial ideal
    --L2 list of monomials
    --return list of monomial ideals I' where 
    --I' is an ideal I in L1 with a monomial from L2 adjoined 
    --that is not in the ideal I
    --
    --sorted.
    unique flatten for I in L1 list (
        for m in L2 list (
            if m %  I != 0 then I+monomialIdeal m
            else continue
            )
        )
    )
sumMonomials(Ideal, List) := List => (I, L2) -> sumMonomials({I}, L2)

normalForms = method()
normalForms(List, List) := (Fs, G) -> (
    <<"---"<< #Fs<<endl;
    -- Fs is a list of MonomialIdeals, G a list of ring maps
    -- returns a minimal subset F of Fs such that G F = Fs.
    if #Fs == 0 then return {};
    S := ring Fs_0;
    G1 := select(G, s -> s vars S != vars S); -- remove the identity element if present.
    L := new MutableList from Fs;
 --elapsedTime 
    LH := hashTable for i from 0 to #Fs-1 list Fs#i => i;
    count := #L;
    if debugLevel > 0 then << "-- " << #L << " ideals" << endl;

 --elapsedTime 
    ans := for i from 0 to #L-1 list (
        if L#i === null then continue;
        F := L#i;
        for f in G1 do (
            H := monomialIdeal(f F);
            if LH#?H then (
                j := LH#H;
                if j > i and L#j =!= null then (
                    L#j = null;
                    count = count - 1;
                    if count % 1000 == 0 and debugLevel > 0 then
                        << "--  remaining count: " << count << endl;
                    );
                );
            );
        F
        )
    )

--The Lis versions:

toLis = method()
--should always be a list of lists. The zero monomial ideal is () and this has to be handled separately.
toLis RingElement := List => m -> (exponents m)_0
toLis MonomialIdeal := List => I -> if I == 0 then {{}} else 
                                    --reverse sort( I_*/(m-> toLis m))
				    sort( I_*/(m-> toLis m))

toMonLis = (S,e) -> product(#e, i-> S_i^(e_i))
fromLis = method()
fromLis (Ring, List) := MonomialIdeal => (S,L) -> if L === {} then monomialIdeal 0_S else 
                                                              monomialIdeal apply(L,e-> toMonLis (S,e))

notIn = method()
notIn(List, List) := Boolean => (m, L2) -> (
    --m a list of n elements corresponding to a monomial m in S
    --L2 a list of lists of such, corresponding to a monomial ideal I
    --returns true if m is not in I.
    if L2 == {{}} then return true;
    diffs := apply(L2, n -> m-n);
    all(diffs, L -> min L < 0)
    )

squareFreeLis = method()
squareFreeLis(VisibleList, Ring) := List => (d,R) -> (
    if degreeLength R != #d then 
        error("expected degrees of length "|degreeLength R);
    z := symbol z;
    R' := coefficientRing R[z_1..z_(numgens R), SkewCommutative => true, Degrees => degrees R];
    phi := map(R,R',vars R);
    toLis monomialIdeal phi basis(d,R')
    )
squareFreeLis(ZZ, Ring) := Matrix => (d,R) -> squareFreeLis({d}, R)

monomialsInDegreeLis = method()
monomialsInDegreeLis (VisibleList,Ring,String) := 
monomialsInDegreeLis(ZZ, Ring, String) := List => (d, R, type) -> (
    -- d: integer, or list (multidegree).
    -- R: polynomial ring
    -- type is either "All", "SquareFree" (anything else is an error)
    -- return: is a matrix of monomials of the given type and degree
    flatten entries sort(monomialsInDegree(d,R,type), MonomialOrder => Descending)/toLis
    )

orbitRepresentatives = method(Options=>{MonomialType => "All"})
orbitRepresentatives(Ring, Ideal, VisibleList) := List => o -> (R, I, degs) -> (

    if not isMonomialIdeal I then error"orbitRepresentatives:arg 1 is not a monomial ideal";
    result := {toLis monomialIdeal I}; --if I = 0, this gives {{}} ; has to be treated specially

    if #degs >1 then  degs = sort toList(degs); -- more efficient to add the small degree gens first.

    n := numgens R;
    G := permutations n;

    for d in degs do( 
--	<<"------"<<endl;
        mons := monomialsInDegreeLis(d, R, o.MonomialType);
--     elapsedTime 
	sumList := sumMonomialsLis(result, mons);
--	<<#result<<" "<<#sumList<<endl;
--     elapsedTime 
	result = normalFormsLis(sumList, G);
--        result = normalFormsLis(sumMonomialsLis(result, mons), G); -- was reverse sort
    	);
     result/(L -> fromLis(R,L))
    )


orbitRepresentatives(Ring, VisibleList) := List => o -> (R, degs) -> (
    ze := monomialIdeal 0_R;
    orbitRepresentatives(R, ze, degs, o)
    )
///
restart
loadPackage "MonomialOrbits"
debug MonomialOrbits
S = ZZ/101[a..d];
L = orbitRepresentatives(S,(2,2,2))
L = orbitRepresentatives(S,{2,2,2}, MonomialType => "SquareFree")
monomialsInDegreeLis(2,S,"SquareFree")
tally apply(L, m->betti res m)
///

orbitRepresentatives(Ring, Ideal, Ideal, ZZ) := List => o -> (R, I, startmons, numelts) -> (
     --take or subtract numelts elements from startmons mod I, plus I.

    if not isMonomialIdeal I then error"orbitRepresentatives:arg 1 is not a monomial ideal";
    I = monomialIdeal I;

    if not isMonomialIdeal startmons then error"orbitRepresentatives:arg 2 is not a monomial ideal";
    startmons = monomialIdeal startmons;

    n := numgens R;
    G := permutations n;

    num := abs(numelts);
    
    Ilis := toLis monomialIdeal I;
    startLis := toLis monomialIdeal startmons;
    start := if Ilis ==={{}} then startLis else
             for m in startLis list if notIn(m,Ilis) then m else continue;

   result := {Ilis}; --if I = 0, this gives {{}} ; has to be treated specially   
   mons := start;

    apply(num, i-> (
	sums := sumMonomialsLis(result, mons);
	result = normalFormsLis(sums, G)
        ));

if numelts < 0 then (
-- use the previously computed "result" to subtract.
-- basically: subtract Ilis from result to get result0, then subtract result0 from start to get result.
	result0 := for J in result list subtract(J, Ilis);
	result = for K in result0 list subtract(start,K);
    );
    apply(result, L -> fromLis(R,L))
    )


orbitRepresentatives1 = method(Options => {MonomialType => "All"})
orbitRepresentatives1(Ring, Ideal, Ideal, ZZ) := List => o -> (R, I, startmons, numelts) -> (
     --take or subtract numelts elements from startmons mod I, plus I.

    if not isMonomialIdeal I then error"orbitRepresentatives:arg 1 is not a monomial ideal";
    I = monomialIdeal I;

    if not isMonomialIdeal startmons then error"orbitRepresentatives:arg 2 is not a monomial ideal";
    startmons = monomialIdeal startmons;

    n := numgens R;
    G := permutations n;

    num := abs(numelts);
    
    Ilis := toLis monomialIdeal I;
    startLis := toLis monomialIdeal startmons;
    start := if Ilis ==={{}} then startLis else
             for m in startLis list if notIn(m,Ilis) then m else continue;

---if I is large it *might* make sense to add ILis at the end, instead of here
   result := {Ilis}; --if I = 0, this gives {{}} ; has to be treated specially   
   mons := start;

    apply(num, i-> (
	sums := sumMonomialsLis(result, mons);
	result = normalFormsLis(sums, G)
        ));

if numelts < 0 then (
-- use the previously computed "result" to subtract.
-- basically: subtract Ilis from result to get result0, then subtract result0 from start to get result.
	result0 := for J in result list subtract(J, Ilis);
	result = for K in result0 list subtract(start,K);
    );

    apply(result, L -> fromLis(R,L))
    
    )

--FIX ME: the following takes significant time; is there a faster way?
subtract = method()
subtract (List, List) := List => (L,M) -> sort toList(set L - set M)
    --L and M are monomial ideals with generators of the same degree, represented as lists of lists 
    --we return sort toList(set L sett M) , the equivalent of monomialIdeal (gens L % M).

sumMonomialsLis = method()
sumMonomialsLis(List, List) := List => (L1, L2) -> (
    --L1 list of lists of lists, representing a list of monomial ideals, or a list representing a single
    --monomial ideal.
    --L2 list of lists, representing monomials
    --return list of lists L of lists; where 
    --L representa a monomial ideal L' in L1 with a "monomial" from L2 adjoined 
    --that is not divisible by any monomial in L',
    --sorted.
    unique flatten for I in L1 list (
        for m in L2 list if I == {{}} then {m} else
            if notIn(m, I) then sort (I | { m }) --do we need to sort here too?	    
            else continue
            ))
    
normalFormLis = method()
normalFormLis (List, List) := List => (F,G) -> (
    --F a list of lists representing a single ideal
    --G a list of lists representing permutations
    first sort for g in G list sort apply(F, FF->FF_g))

orbitRepresentativesExperiment = method(Options=>{MonomialType => "All"})
orbitRepresentativesExperiment (Ring, Ideal, VisibleList) := List => o -> (R, I, degs) -> (
    if not isMonomialIdeal I then error"orbitRepresentatives:arg 1 is not a monomial ideal";
    result := {toLis monomialIdeal I}; --if I = 0, this gives {{}} ; has to be treated specially
    if #degs >1 then  degs = sort toList(degs); -- more efficient to add the small degree gens first.
    n := numgens R;
    G := permutations n;

    for d in degs do( 
        mons := monomialsInDegreeLis(d, R, o.MonomialType);
	sumList := sumMonomialsLis(result, mons);
	result = unique apply(sumList, F -> normalFormLis(F,G));
    	);
     result/(L -> fromLis(R,L))
    )

normalFormsLis = method()
normalFormsLis(List, List) := List => (Fs, G) -> (
    -- Fs is a list of lists representing MonomialIdeals, G a list of permutations
    -- returns a minimal subset F of Fs such that G F = Fs.
    if #Fs == 0 then return {{}};

    n := #(Fs_0_0); -- "number of variabes"
    ident := apply(n, i-> i);
    G1 := select(G, g-> g != ident); -- remove the identity element if present.

   
    L := new MutableList from Fs;
    LH := hashTable for i from 0 to #Fs-1 list Fs#i => i;
    count := #L;
    if debugLevel > 0 then << "-- " << #L << " ideals" << endl;

    ans := for i from 0 to #L-1 list (
        if L#i === null then continue;
        F := L#i;
        for f in G1 do (
            H := sort apply(F, FF -> FF_f);
            if LH#?H then (
                j := LH#H;
                if j > i and L#j =!= null then (
                    L#j = null;
                    count = count - 1;
                    if count % 1000 == 0 and debugLevel > 0 then
                        << "--  remaining count: " << count << endl;
                    );
                );
            );
        F
        );
    ans
    )

    

beginDocumentation()

doc ///
    Key
        MonomialOrbits
    Headline
        find orbit representatives of monomial ideals, under permutations of the variables
    Description
        Text
            This package contains functions for the construction of
            representatives of the orbits of monomial ideals of a
            given type in a polynomial ring $S$ under the group of
            permutations of the variables of $S$.
            
            The type of the ideals may be defined either by the number
            of minimal generators of each degree, or by
	    the set of monomials from which to choose 
	    or by the set of monomials from which to
	    subtract in @TO
            orbitRepresentatives @ or by the Hilbert function, in @TO
            hilbertRepresentatives@.  If the option {\tt MonomialType
            => "SquareFree"} is given, then only square-free monomial
            ideals are considered.
    Subnodes                                         
        :Enumerating monomial ideals with given generator degrees or number of elements
            @TO orbitRepresentatives@
        :Enumerating monomial ideals with given Hilbert function
            @TO hilbertRepresentatives@
        :Options limiting the type of ideals generated and whether to add or subtract monomials
            @TO MonomialType@ 
///

doc ///
    Key
        orbitRepresentatives
        (orbitRepresentatives, Ring, VisibleList)
        (orbitRepresentatives, Ring, Ideal, VisibleList)
        (orbitRepresentatives, Ring, Ideal, Ideal, ZZ)	
        [orbitRepresentatives, MonomialType]    
    Headline
        find representatives of monomial ideals under permutations of variables
    Usage
        L = orbitRepresentatives(R, degs)
        L = orbitRepresentatives(R, I, degs)
	L = orbitRepresentatives(R, I, J, numelts)
    Inputs
        R:PolynomialRing
        degs:List 
            or @ofClass Sequence@, of the degrees of the generators
        I:Ideal
            The starting ideal; all the ideals returned will contain this one.
	J:Ideal
	    A monomial ideal containing monomials from which to add to I;
	    when numelts < 0, then the ideals formed are I+J minus 
	    a certain number of monomials.
	numelts:ZZ
	    If numelts >0 then each monomial ideal produced is
	    I+ numelts elements of J; if numelts < 0 then 
	    each monomial ideal produced is I+J minus |numelts| elements of J.
        MonomialType => String
            (either {\tt "All"} or {\tt "SquareFree"}).  For {\tt "All"}, 
            all monomials are
            considered, and for {\tt "SquareFree"},
            only square free monomials are considered
    Outputs
        L:List
            of monomial ideals
    Description
        Text
            This method generates a list of representatives of the orbits of
            monomial ideals with given minimal generator degrees
            under the group of permutations of the variables.

            If the option @TO MonomialType@ is set to "SquareFree",
            then only ideals of square-free monomials are considered.

            The program works by induction on the number of
            generators; given the list L of orbit representatives for
            the ideals minimally generated by the first k of the
            generators, the program adds all possible generators of
            the (k+1)-st degree to each of ideals in L in a certain
            order, and then removes those in the list that can be
            obtained by a permutation of variables from one that is earlier
            in the list.
	    
            Because the generators are constrained to be minimal generators,
            it is advantageous to specify the low degrees of generators first.  

            Note that {\tt degs} is specified as a VisibleList, which could
            be either a list or a sequence.
        Example
            S = ZZ/101[a..d];
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
            Multi-gradings are also allowed:
        Example
            S = ZZ/101[x_0..x_3, Degrees=>{{1,2},{2,1},{1,1},{1,0}}];
            orbitRepresentatives(S,{{2,2},{2,1}})
        Text
            Since the input data specifies degrees of minimal generators,
            the set of ideals may be empty:
        Example
            S = ZZ/101[a,b];
            L = orbitRepresentatives(S,(2,2,2,2))
	Text
	    It is possible to give a starting monomial ideal, and add
	    a given number of its generators.
	Example
            L = orbitRepresentatives(S,monomialIdeal a^3, (ideal(a,b))^3, 2)
	Text
	    If the number given is negative, then all but that number
	    of elements of the starting monomial ideal in arg 2 are taken. The 
	    starting monomial ideal is reduced mod the ideal in arg 1 before
	    the process begins
	Example
	    L = orbitRepresentatives(S,monomialIdeal a^3, (ideal(a,b))^3, -2)
    SeeAlso
        hilbertRepresentatives
        MonomialType
///

doc ///
    Key
        hilbertRepresentatives
        (hilbertRepresentatives, Ring, VisibleList)
        [hilbertRepresentatives, MonomialType]    
    Headline
        find representatives of monomial ideals under permutations of the variables
    Usage
        L = hilbertRepresentatives(R,s)
    Inputs
        R:PolynomialRing
        s:VisibleList 
            of desired values of {\tt d->hilbertFunction(R/I,d)} for d in (1..length s)
        MonomialType => String
            (either {\tt "All"} or {\tt "SquareFree"}).  For {\tt "All"}, 
            all monomials are
            considered, and for {\tt "SquareFree"},
            only square free monomials are considered
    Outputs
        L:List
            of monomial ideals
    Description
        Text
            This method generates a list of representatives of the orbits of
            monomial ideals with given Hilbert function, 
            under the group of permutations of the variables.

            If the option @TO MonomialType@ is set to "SquareFree",
            then only ideals of square-free monomials are considered.

            Starting with orbit representatives of monomial ideals
            generated by all but s_0 linear forms, it successively adds to each 
            monomial ideal already found as
            many forms of degree d in (2..1+length s) as necessary to
            achieve the desired Hilbert function, in all possible ways.  After each addition
            it chooses representatives under the action of the group permuting the
            variables of the ring.

            Note that the (partial) Hilbert function is specified as a
            @TO VisibleList@, which could be either a list or a sequence.
        Example
            S = ZZ/101[a..d];
            netList(L = hilbertRepresentatives(S,{4,7,10}))
            #L
            tally apply(L, m-> hilbertPolynomial(m,Projective => false))
            tally apply(L, m->betti res m)	    
	    tally apply(L, m->primaryDecomposition m)	    
	Text
            If the option @TO MonomialType@ is set to "SquareFree",
            then only ideals of square-free monomials are considered.
        Example
    	    netList hilbertRepresentatives(S,{4,7,10,13}, MonomialType => "SquareFree")
        Text
            It is possible to specify data which results in no ideals:
        Example
            S = ZZ/101[a,b];
            hilbertRepresentatives(S,{1,4}) == {}
    SeeAlso
        orbitRepresentatives
        MonomialType
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
            The default is "All".
///
TEST///
debug MonomialOrbits
#(G = permutations 4)
#(G1 = drop(G,1))
Fs = {{{1, 0, 0, 0}, {0, 0, 0, 1}, {0, 0, 1, 0}}, {{1, 0, 0, 0}, {0, 0, 0, 1}, {0, 1, 0, 0}}, {{1, 0, 0, 0}, {0, 0, 1, 0}, {0, 1, 0, 0}}}
Fs = Fs/sort
assert(#normalFormsLis(Fs,G) == 1) 
///    

TEST///
debug MonomialOrbits
S = ZZ/101[x,y,z]
L = monomialsInDegreeLis(4,S,"All")
M = monomialsInDegree(4,S,"All")
M' = sort(M, DegreeOrder => Ascending, MonomialOrder => Descending)
assert(all(#L, i->toMonLis(S, L_i) === (flatten entries M')_i))
///

TEST///
restart
loadPackage"MonomialOrbits"
debug MonomialOrbits
S = ZZ/101[x,y,z]
L = monomialsInDegreeLis(4,S,"All")
M = monomialsInDegree(4,S,"All")
M' = sort(M, DegreeOrder => Ascending, MonomialOrder => Descending)
assert(all(#L, i->toMonLis(S,L_i) === (flatten entries M')_i))
///

TEST///
  S = ZZ/101[x_0..x_3, Degrees=>{{1,2},{2,1},{1,1},{1,0}}]

  result = orbitRepresentatives(S,{{2,2},{2,1}})
  ans = {monomialIdeal(x_1, x_0*x_3), 
      monomialIdeal(x_2*x_3, x_0*x_3),
      monomialIdeal(x_1, x_2^2),
      monomialIdeal(x_2*x_3, x_2^2)}
  assert(#result == 4)
  assert(set ans === set result)
///

TEST///
  S = ZZ/101[a,b,c]
  I = monomialIdeal"a3,b3,c3"
  assert(#orbitRepresentatives(S,{3,3,3}) == 25)
  assert(#orbitRepresentatives(S,I,{3}) == 2)
  assert(#orbitRepresentatives(S,monomialIdeal 0_S, (monomialIdeal vars S)^3, 3) == 25)
  assert(#orbitRepresentatives(S,I, (monomialIdeal vars S)^3, 1) == 2)
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
  assert(# permutations S == 24)
///
///
restart
debug loadPackage("MonomialOrbits", Reload=>true)
///

TEST///   
S = ZZ/101[a..d]
mm = monomialIdeal gens S
assert ({monomialIdeal (b, c)} ==
     orbitRepresentatives(S, monomialIdeal S_0, mm, -1)
     )
assert (
     #orbitRepresentatives(S, monomialIdeal S_0, mm, -1) == 1
     )
 assert(
    {monomialIdeal(b^2,b*c,c^2,b*d,c*d), monomialIdeal(b^2,b*c,c^2,b*d,d^2)} ==
    orbitRepresentatives(S, monomialIdeal S_0, mm^2, -1)
    )
assert({monomialIdeal (a, d)} == 
       orbitRepresentatives(S, monomialIdeal S_0, mm, 1)
       )
assert(
      {monomialIdeal(a,c*d,d^2), monomialIdeal(a,c^2,d^2), monomialIdeal(a,b*c,d^2), monomialIdeal(a,b*d,c*d)} == 
      orbitRepresentatives(S, monomialIdeal S_0, mm^2, 2)
      )
///


///--new TEST
restart
loadPackage "MonomialOrbits"
debugLevel = 1
///

TEST///
debug MonomialOrbits;
S = ZZ/101[x,y,z]
mm = ideal vars S
I = monomialIdeal monomialsInDegree(3,S,"All")
L = toLis I
assert(I_* == (fromLis(S, toLis I))_*)
ze = monomialIdeal 0_S

ans1 = orbitRepresentatives(S,ze, {2,2}) -- both of these pairs should be singletons:
ans2 = orbitRepresentatives(S,ze, {2,2}) -- both of these pairs should be singletons:
assert(ans1==ans2)

ans1 = orbitRepresentatives(S,ze, {3}) 
ans2 = orbitRepresentatives(S,ze, {3})
assert(ans1==ans2)

ans1 = orbitRepresentatives(S,monomialIdeal(x^3), {3})
ans2 = orbitRepresentatives(S,monomialIdeal(x^3), {3})
assert(ans1==ans2)

ans1 = orbitRepresentatives(S,monomialIdeal(z^3), {3}) 
ans2 = orbitRepresentatives(S,monomialIdeal(z^3), {3})
assert(ans1 == ans2)

ans1 = orbitRepresentatives(S,monomialIdeal(0_S), {3,3})
ans2 = orbitRepresentatives(S,monomialIdeal(0_S), {3,3})
assert(ans1 == ans2)

assert(#orbitRepresentatives (S, ze, 3:5) == 238)

ans1 = orbitRepresentatives (S, ze, {2,3,4})
ans2 = orbitRepresentatives (S, ze, (2,3,4))
assert(ans1 == ans2)
ans3 = orbitRepresentatives (S, {2,3,4})
assert(ans1 == ans3)

assert(#orbitRepresentatives (S, monomialIdeal x, mm, -1) == 1)
assert(#orbitRepresentatives (S, ze, mm, -1) == 1)
///

end---------------------------------------------------------------------

///
  restart
  loadPackage("MonomialOrbits", Reload => true)
  uninstallPackage "MonomialOrbits"
  restart
  installPackage "MonomialOrbits"
  check "MonomialOrbits"

  viewHelp MonomialOrbits
///



n = 4
x = symbol x
S = ZZ/101[x_1..x_n]
ze = monomialIdeal  0_S
mm = monomialIdeal gens S
debug MonomialOrbits
d = 5;s = 2 --old timing 1.1 sec, (56, 1540),  90 examples Lis version .1 sec
d = 5;s = 3 --old timing 17 sec, (56, 27720), 1282 exmamples Lis version 1.7 sec
d= 4;s=8

#elapsedTime orbitRepresentatives (S, ze, s:d) --s=d=4 in 1.67 sec, 2380 examples.
--old timing 41.5 sec, (35, 52360), 2380 examples Lis version 4.44 sec
#elapsedTime orbitRepresentatives (S, ze, mm^d, s) 

#elapsedTime orbitRepresentatives (S, ze, mm^d, -s) --4.5 sec

--How many of these ideals are there?
there are about 20 million examples with n=d=4, s = 13

binomial(n+d-1, n-1), inter = binomial(n+d-1, n-1)-n*(d+1)+n*(n-1) 
binomial (inter,  s)


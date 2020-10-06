act = method()

-- g is a permutation on a list of integers 0..#g-1
-- L is a list of integers in the range 0..#g-1 (possibly repeated).
-- returns g(L), the action of the permutation g on the list L of elements.
act(List, List) := (g, L) -> L/(i -> g#i)//sort

orbit = method()
orbit(List, List) := (L, G) -> sort unique for g in G list act(g,L)

sums = method()
sums(List, List) := (L1, L2) -> (
    -- L1 is a list of list of integers, L2 is a list of integers
    -- for each set f in L1, for each a element in L2:
    --   if a is not in f, then place sort(f,a) on output.
    sort unique flatten for f in L1 list (
        sf := set f;
        for a in L2  list (
            if not member(a, sf) then sort append(f, a) else continue
        )
    )
)

normalForms = method()
normalForms(List, List) := (Fs, G) -> (
    -- Fs is a list of list of ints
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
            H := act(f, F);
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

addGenerator = method()
addGenerator(List, List, List) := (Ls, L, G) -> normalForms(sums(Ls, L), G)
    
setupRing = method()
setupRing(ZZ, ZZ) := (numvars, deg) -> (
    -- for us, generally deg is 3.
    -- output: (ring, Sn, monomLists, allMonoms)
    R := ZZ/2[vars(0..numvars-1)];
    perms := permutations numvars;
    B := basis(deg, R);
    B = B_(reverse sortColumns B);
    Sn := for p in perms list (
        f := map(R, R, (vars R)_p);
        reverse sortColumns (f B)
        );
    M := toList(0..numColumns B-1);
    B = flatten entries B;
    orbitReps := flatten normalForms(for i from 0 to #B-1 list {i}, Sn);
    orbits := orbitReps/(x -> orbit({x}, Sn))/flatten;
    (R, Sn, orbits, B)
    )

setupRing = method()
setupRing(Ring, List) := List => (S, deg) -> (
    perms := permutations numgens S;
    iB := for d in deg list
        sort(basis(d, S), DegreeOrder => Ascending, MonomialOrder => Descending);
    B := matrix{iB};
    Sn := for p in perms list (
        f := map(S, S, (vars S)_p);
        sortColumns(f B, DegreeOrder => Ascending, MonomialOrder => Descending)
        );
    B = flatten entries B;
    IB := hashTable for d in deg list d => positions(B, m -> first degree m == d);
    (Sn, B, IB)
    )

end--
restart
needs "monomial-orbits.m2"

(S, S3, orbs, B) = setupRing(3, 3);

d3 = toList(0..9)
nf1 = addGenerator({{}}, d3, S3)
nf2 = addGenerator(nf1, d3, S3)
nf3 = addGenerator(nf2, d3, S3)
nf4 = addGenerator(nf3, d3, S3);
elapsedTime nf5 = addGenerator(nf4, d3, S3);
elapsedTime nf6 = addGenerator(nf5, d3, S3);
elapsedTime nf7 = addGenerator(nf6, d3, S3);
elapsedTime nf8 = addGenerator(nf7, d3, S3);
elapsedTime nf9 = addGenerator(nf8, d3, S3);
elapsedTime nf10 = addGenerator(nf9, d3, S3);
elapsedTime nf11 = addGenerator(nf10, d3, S3);

-- allow several in each degree
-- (1) combine all degrees of interest
--     also note each degrees index range.
-- (2) create the symmetric group on this index set
--     

S = ZZ/2[a,b,c,d]
(S4, B, IB) = setupRing(S, {2,3,4});
nf1 = addGenerator({{}}, IB#2, S4)
nf2 = addGenerator(nf1, IB#3, S4)
nf3 = addGenerator(nf2, IB#3, S4)
nf3/(p -> B_p)/ideal

-- 3 distinct cubics in S
nf1 = normalForms(addNewMonomial({{}}, toList(0..9)), S3)
  all2 = addNewMonomial(nf1, toList(0..9))
nf2 = normalForms(all2, S3)
  all3 = addNewMonomial(nf2, toList(0..9))
nf3 = normalForms(all3, S3)
  all4 = addNewMonomial(nf3, toList(0..9))
nf4 = normalForms(all4, S3)

  d3 = toList(0..9)
  all1 = sums({{}}, d3)
nf1 = normalForms(all1, S3)
  all2 = sums(nf1, d3)
nf2 = normalForms(all2, S3)
  all3 = sums(nf2, d3)
nf3 = normalForms(all3, S3)
  all4 = sums(nf3, d3)
nf4 = normalForms(all4, S3)





perms = permutations 4
B2 = sort(basis(2, S), DegreeOrder => Ascending, MonomialOrder => Descending)
B3 = sort(basis(3, S), DegreeOrder => Ascending, MonomialOrder => Descending)
B4 = sort(basis(4, S), DegreeOrder => Ascending, MonomialOrder => Descending)
B = B2 | B3 | B4
assert(toList(0..numcols B - 1) == sortColumns(B, DegreeOrder => Ascending, MonomialOrder => Descending))
S4 = for p in perms list (
        f := map(S, S, (vars S)_p);
        sortColumns(f B, DegreeOrder => Ascending, MonomialOrder => Descending)
        );
B = flatten entries B
degs = B/degree/first//unique//sort
M = hashTable for d in degs list d => positions(B, m -> first degree m == d)

d2 = positions(B, m -> first degree m == 2)
d3 = positions(B, m -> first degree m == 3)

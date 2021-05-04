taylorResolution = method(
    Options => {LengthLimit => 0}
    )

taylorResolution(MonomialIdeal):= ChainComplex => o -> (I)->(
    --- this function just returns the Koszul complex
    --- where I represents the first differential.
    if not instance(o.LengthLimit, ZZ)
    then error "The optional LengthLimit must be an integer.";
    lengthLimit := 0;
    if (o.LengthLimit == 0) then
       lengthLimit = numgens I
    else
       lengthLimit = o.LengthLimit;
    chainComplex(apply((1..lengthLimit), i -> taylorResolution(i,I)))
)

lcmlist = L -> L//transpose/max
taylorResolution(ZZ,MonomialIdeal) := Matrix => o-> (d,I) -> (
    if d === 1 then return gens I;
    
    S := ring I;
    Ilists := flatten(I_*/exponents);
    btarget := subsets(toList(0..#Ilists-1), d-1);
    bsource := subsets(toList(0..#Ilists-1), d);
    degtarget := apply (subsets( Ilists, d-1),s -> sum lcmlist s);
    degsource := apply (subsets( Ilists, d),s -> sum lcmlist s);

    rows := hashTable for i from 0 to #btarget-1 list (
        b := btarget#i;
        blcm := lcmlist Ilists_b;
        b => {i, blcm}
        );

    cols := hashTable for i from 0 to #bsource-1 list (
        b := bsource#i;
        blcm := lcmlist Ilists_b;
        b => {i, blcm}
        );

    rcpairs := flatten apply(bsource, b-> apply(#b, i->(b,drop(b,{i,i}), (-1)^i)));

    monomsS := new MutableHashTable;
    elems := apply(rcpairs,
            p -> (
                r := rows#(p_1); -- {index, lcm}
                c := cols#(p_0);
                e := c#1 - r#1;
                mylcm = if not monomsS#?e then 
                           monomsS#e = S_e
                        else 
                           monomsS#e;
                (r#0, c#0) => p_2 * mylcm
                ));
    map(S^(-degtarget), S^(-degsource), elems)
    )

///
restart
load "taylor.m2"
///
TEST///
S = ZZ/101[a,b,c]
I = monomialIdeal"a3bc,a2b3,ab2c2,a2c3"
T = taylorResolution I
assert(isHomogeneous T)
assert(prune HH T == gradedModule coker gens I)
assert(T.dd^2 == 0)
I = monomialIdeal(basis(3,S))
T = taylorResolution I
assert(isHomogeneous T)
assert(prune HH T == gradedModule coker gens I)
assert(T.dd^2 == 0)
///
end--


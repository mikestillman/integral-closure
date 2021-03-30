
myLcm = method()
myLcm(List):=(ringList)->(
   --- just a short method computing the lcm of the list of elements
   myList := apply(ringList, i -> ideal(i));
   (intersect myList)_0
)

taylor = method()
taylor(ZZ,MonomialIdeal):= (n,I)->(
   --- create the nth differential in Taylor's resolution
   retVal := Nothing;
   if (n == 1) then 
      retVal = gens I
   else
   {
      idealList := flatten entries gens I;
      R := ring I;
      sourceSubsets := subsets(toList (0..(numgens I - 1)),n);
      targetSubsets := subsets(toList (0..(numgens I - 1)),n-1);
      sourceList := apply(sourceSubsets, i -> myLcm(idealList_i));
      targetList := apply(targetSubsets, i -> myLcm(idealList_i));
      getCoeff := (i,j) -> if (isSubset(targetSubsets_i,sourceSubsets_j)) then
                             (-1)^(position(sourceSubsets_j, 
				     k -> k == (toList(set sourceSubsets_j - set targetSubsets_i))_0))
			   else 0_R;
      myFn := (i,j) -> (tempElt := sourceList_j / targetList_i;
	                if (liftable(tempElt,R)) then getCoeff(i,j)*lift(tempElt,R) else 0_R);
      retVal = map(R^(-apply(targetList, i -> degree i)), R^(-apply(sourceList, i -> degree i)), myFn);
   };
   retVal
)

taylorResolution=method(
    Options => {LengthLimit => 0}
)
taylorResolution(MonomialIdeal):= o -> (I)->(
    --- this function just returns the Koszul complex
    --- where I represents the first differential.
    if not instance(o.LengthLimit, ZZ)
    then error "The optional LengthLimit must be an integer.";
    lengthLimit := 0;
    if (o.LengthLimit == 0) then
       lengthLimit = numgens I
    else
       lengthLimit = o.LengthLimit;
    chainComplex(apply((1..lengthLimit), i -> taylor(i,I)))
)


lcmlist = L -> L//transpose/max
newTaylor = method()
newTaylor(ZZ,MonomialIdeal) := Matrix => (d,I) -> (
    S := ring I;
    Ilists = flatten(I_*/exponents);
    btarget = subsets(toList(0..#Ilists-1), d-1);
    bsource = subsets(toList(0..#Ilists-1), d);
  
    elapsedTime (  
    degtarget = apply (subsets( Ilists, d-1),s -> sum lcmlist s);
    degsource = apply (subsets( Ilists, d),s -> sum lcmlist s);
    );
    
    rows = hashTable for i from 0 to #btarget-1 list btarget#i => i;
    cols = hashTable for i from 0 to #bsource-1 list bsource#i => i;          

    elapsedTime rcpairs = flatten apply(bsource, b-> apply(#b, i->(b,drop(b,{i,i}), (-1)^i)));
    elapsedTime elems := apply(rcpairs,
            p -> (rows#(p_1), cols#(p_0)) => 
                    p_2*S_(lcmlist Ilists_(p_0) - lcmlist Ilists_(p_1)));
    elapsedTime map(S^(-degtarget), S^(-degsource), elems)
    )

newTaylor(ZZ,MonomialIdeal) := Matrix => (d,I) -> (
    S := ring I;
    Ilists = flatten(I_*/exponents);
    btarget = subsets(toList(0..#Ilists-1), d-1);
    bsource = subsets(toList(0..#Ilists-1), d);
  
    elapsedTime (  
    degtarget = apply (subsets( Ilists, d-1),s -> sum lcmlist s);
    degsource = apply (subsets( Ilists, d),s -> sum lcmlist s);
    );
    
    rows = hashTable for i from 0 to #btarget-1 list btarget#i => i;
    cols = hashTable for i from 0 to #bsource-1 list bsource#i => i;          

    elapsedTime rcpairs = flatten apply(bsource, b-> apply(#b, i->(b,drop(b,{i,i}), (-1)^i)));

    elapsedTime (    
    rowLcms = for b in btarget list lcmlist Ilists_b;
    colLcms = for b in bsource list lcmlist Ilists_b;
    );
    
    elapsedTime elems := apply(rcpairs,
            p -> (rows#(p_1), cols#(p_0)) => 
                    p_2*S_(colLcms#(cols#(p_0)) - rowLcms#(rows#(p_1))));
                
    elapsedTime map(S^(-degtarget), S^(-degsource), elems)
    )
-- above version is twice as fast as one above that.

newTaylor(ZZ,MonomialIdeal) := Matrix => (d,I) -> (
    S := ring I;
    Ilists = flatten(I_*/exponents);
    
    btarget = subsets(toList(0..#Ilists-1), d-1);
    bsource = subsets(toList(0..#Ilists-1), d);
  
    degtarget = apply (subsets( Ilists, d-1),s -> sum lcmlist s);
    degsource = apply (subsets( Ilists, d),s -> sum lcmlist s);

    rows = hashTable for i from 0 to #btarget-1 list (
        b := btarget#i;
        blcm := lcmlist Ilists_b;
        b => {i, blcm}
        );

    cols = hashTable for i from 0 to #bsource-1 list (
        b := bsource#i;
        blcm := lcmlist Ilists_b;
        b => {i, blcm}
        );

    rcpairs = flatten apply(bsource, b-> apply(#b, i->(b,drop(b,{i,i}), (-1)^i)));

    monomsS = new MutableHashTable;
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
    << "#elems = " << #elems << " and #monomsS = " << #(keys monomsS) << endl;
                
    Ftar := S^(-degtarget);
    Fsrc := S^(-degsource);
    
    map(Ftar, Fsrc, elems)
    )


///
restart
load "taylor.m2"
needsPackage "Complexes"
S = ZZ/101[a,b,c]
I = monomialIdeal"a3bc,a2b3,ab2c2,a2c3"
I = monomialIdeal(basis(3,S))
I = monomialIdeal(basis(4,S))
elapsedTime taylorResolution I
elapsedTime K = complex for i from 2 to numgens I list elapsedTime newTaylor(i,I)
elapsedTime newTaylor(8, I);
K.dd^2
isHomogeneous K

elapsedTime for i from 0 to 50000 do S_{1,3,2};
elapsedTime newTaylor(7,I);
///
end--
restart
load "taylor.m2"
kk = ZZ/101
S = kk[a,b,c]
I = monomialIdeal basis(2,S)
elapsedTime T = taylorResolution I
apply (10, j-> elapsedTime T = taylor(j+1,I));
elapsedTime K =  koszul gens I
K3 = matrix {apply (numcols K.dd_3, i-> syz transpose syz transpose K.dd_3_{i})};
K3' = taylor(3,I);
K3
K3'
I_*
taylor(2,I)

restart
loadPackage "ChainComplexExtras"
debug Core
--for L a list of lists:
lcmlist = L -> L//transpose/max


S = kk[a,b,c]
I = monomialIdeal"a3bc,a2b3,ab2c2,a2c3"
I = monomialIdeal basis(3,S)
Ilists = flatten(I_*/exponents)
elapsedTime ents = for i from 1 to numgens I list apply(subsets( Ilists, i), s -> S_(lcmlist s));
elapsedTime for i from 2 to numgens I list map(S,rawKoszulMonomials(0,raw matrix{ents_(i-2)}, raw matrix{ents_(i-1)}));

elapsedTime (taylorResolution I);
matrix{ents_(i-1)}
debug Core

T = kk[a,b,c, DegreeRank => 3]
K = koszul(matrix {toList (numgens I:1_T)})
Ilists = flatten(I_*/exponents)
lcms = apply(length K, i -> apply (subsets( Ilists, i+1), s -> lcmlist s));
KK = apply(lcms, ell -> T^(-ell))
elapsedTime C = chainComplex for i from 1 to length K - 2 list map(KK_i,KK_(i+1), K.dd_(i+2));
sparseMatrix C.dd_5;
elapsedTime map(target oo, source oo, entries oo);
X = new MutableMatrix from C.dd_5;
X_(0,0) = 1
X_(0,0)
viewHelp MutableMatrix

map(KK_i,KK_(i+1), K.dd_(i+2)), a)

isHomogeneous homogenize (map(S^{1},S^{-2},1),a)
code methods homogenize
Ilists_{1,2,3}
lcmlist Ilists_{1,2,3,4} - lcmlist Ilists_{1,2,3}
hashTable({({1,2,3},{1,2,3,4}) => S_(lcmlist Ilists_{1,2,3,4} - lcmlist Ilists_{1,2,3})})
viewHelp matrix
help(map, Module, Module, List)

restart


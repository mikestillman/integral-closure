newPackage(
        "NoetherNormalForm",
        Version => "0.1", 
        Date => "9 July 2020",
        Authors => {
            {Name => "David Eisenbud", 
                Email => "de@msri.org", 
                HomePage => "http://www.msri.org/~de/"},
            {Name => "Mike Stillman", 
                Email => "mike@math.cornell.edu", 
                HomePage => "http://www.math.cornell.edu/~mike"}
            },
        Headline => "code for Noether normal forms of affine rings",
        PackageExports => {"NoetherNormalization"},
        DebuggingMode => true
        )

-- creates A --> B, B isomorphic to the original affine ring R/
--   where B is finite over A.
-- frac B --> L
-- coefficientRing B --> A
-- frac A 
-- L --> frac A  (coefficientRing L)
-- L --> B (ring numerator 1_L)
-- noetherField B == L
-- noetherRing L == B
-- how to get the isomorphism from B to R?

export {
    "isFiniteOverCoefficientRing",
    "checkNoetherNormalization",
    "noetherForm",
    "makeFrac",
    "getBasis",
    "getBasisMatrix",
    "inNoetherForm",
    "multiplication",
    "traceForm",
    -- keys used:
    "noetherField",
    "noetherRing",
    "NoetherInfo",
    "Remove"
    }

raw = value Core#"private dictionary"#"raw"
rawIsField = value Core#"private dictionary"#"rawIsField"
isField EngineRing := R -> (R.?isField and R.isField) or rawIsField raw R

--inNoetherForm
inNoetherForm = method()
inNoetherForm Ring := Boolean => (R) -> R.?NoetherInfo

-- private routine
setNoetherInfo = method()
setNoetherInfo(Ring, Ring) := (B, KB) -> (
    B.NoetherInfo = new MutableHashTable;
    KB.NoetherInfo = new MutableHashTable;
    B.NoetherInfo#"noetherField" = KB;
    KB.NoetherInfo#"noetherRing" = B;
      -- this one should contain:
      --   map B --> R (original ring)
      --   map R --> B
      --   map B --> KB
    )

-- private routine
noetherInfo = method()
noetherInfo Ring := (R) -> (
    if not R.?NoetherInfo
    then error "expected a ring or field created with `noetherForm`";
    R.NoetherInfo
    )

noetherField = method()
noetherField Ring := Ring => (R) -> (
    -- Note: any ring created with noetherForm will have this field set.
    -- Two rings are generally created: the noether form itself: B = A[x...]/I
    --  and its fraction field L = k(x...)/I.
    H := noetherInfo R;
    if H#?"NoetherField" 
      then H#"NoetherField" 
      else R
    )

noetherRing = method()
noetherRing Ring := Ring => (R) -> (
    H := noetherInfo R;
    if H#?"NoetherRing" 
      then H#"NoetherRing" 
      else R
    )

-- The following sets (or gets, if already computed) the
-- basis of the ring over its coefficient ring, assuming that
-- the ring has been placed in Noether normal form.
basisOfRing = method()
basisOfRing Ring := (R) -> (
    -- assumption: R is finite over the coefficient ring
    -- returns a matrix over R whose entries are generators
    -- of R over the coeff ring
    NI := noetherInfo R;
    if not NI#?"basis" then (
        LT := leadTerm ideal R;
        K := ultimate(coefficientRing, R);
        R1 := K (monoid R);
     	J := ideal sub(LT,R1);
     	B := sub(cover basis(comodule J), R);
	-- now present this in two ways:
	-- (1) as a list of monomials in R (or, as a matrix?)
	-- (2) as a hash table, m => i, giving the index of each monomial.
	B = sort B;
	L := flatten entries B;
	H := hashTable for i from 0 to #L-1 list L#i => i;
	Rambient := ambient R;
     	S := new MutableHashTable from apply(L, s -> {lift(s,Rambient),s});
        NI#"basis" = B;
        NI#"monomials" = S;
        NI#"inverse basis" = H;
        );
    NI#"basis"
    )

getBasis = method()
getBasis Ring := List => (R) -> first entries (basisOfRing R)

getBasisMatrix = method()
getBasisMatrix Ring := Matrix => (R) -> basisOfRing R

multiplication = method()
multiplication RingElement := (m) -> (
     R := ring m;
     S := getBasisMatrix R;
     (mn, cf) := coefficients(m * S, Monomials => S);
     lift(cf,coefficientRing R)
     )

-- private function.
-- is only called for a noetherField.
setTraces = (R) -> (
     -- R should be a Noether field
    H := noetherInfo R;
    if not H#?"traces" then (
        B := getBasis R;
        traces := for b in B list (
	    m := multiplication b;
	    --numerator lift(trace m, coefficientRing R)
	    t := lift(trace m, coefficientRing R);
	    tdenom := lift(denominator t, coefficientRing ring t);
	    1/tdenom * numerator t
	    );
        H#"traces" = matrix{traces};
        );
    )

trace RingElement := (f) -> (
     -- R = ring f should be a noetherRing or noetherField
     -- result is in the coefficient ring of R.
     R := ring f;
     RK := noetherField R;
     NI := noetherInfo RK;
     if not NI#?"traces" then setTraces RK;
     traces := NI#"traces";
     f = sub(f,RK);
     M := last coefficients(f, Monomials => getBasisMatrix RK);
     g := (traces * M)_(0,0);
     g = lift(g, coefficientRing RK);
     --stopgap for lifts from frac QQ[x] to QQ[x] not working 5-26-11
     --when works, change below to return lift(g, coefficientRing R)
     gdenom := denominator g;
     if gdenom == 1 then numerator g else (
	  gdenom = lift(gdenom, coefficientRing ring gdenom);
	  1/gdenom * numerator g
	  )
     )

traceForm = method()
traceForm Ring := (R) -> (
    RK := noetherField R;
    NI := noetherInfo RK;
    if not NI#?"trace form" then NI#"trace form" = (
        S := getBasis RK;
        K := coefficientRing RK;
        M := mutableMatrix(K, #S, #S);
        for i from 0 to #S-1 do
        for j from i to #S-1 do (
            f := trace(S#i * S#j);
            M_(i,j) = M_(j,i) = f;
            );
        matrix M
        );
    NI#"trace form"
    )

isComputablePolynomialRing = method()
isComputablePolynomialRing Ring := Boolean => R ->(
    --checks whether R is suitable as coefficientRing for a Noether normalization
    --In the future we might want a broader class, for example poly ring over poly ring or a fraction field.
    if not isPolynomialRing R then return false;
    k := coefficientRing R;
    isAffineRing R and
    isField k and
    precision k === infinity and -- eliminates approximate fields RR, CC 
    not instance(k, FractionField)
    )

isFiniteOverCoefficients1 = method()
isFiniteOverCoefficients1 Ring := Boolean => R ->(
   g := gens gb ideal R;
   S := coefficientRing R;
   lt := flatten entries (leadTerm g%promote(ideal vars S,ring g));
   #select(lt/support , l->#l==1) == numgens R
   )
    
TEST/// -- of finiteOverCoefficients
  debug needsPackage "NoetherNormalForm"
  R1 = ZZ/5[a,b][x,y]/intersect(ideal (a*(x-1),y), ideal(x^2,y^2))
  R2 = ZZ/5[a,b][x,y]/intersect(ideal (a*x-1,y), ideal(x^2,y^2))
  R3 = ZZ/5[a,b][x,y]/intersect(ideal ((a-1)*x-1,y), ideal(x^2,y^2))
  R4 = QQ[a,b][x,y]
  R5 = QQ[a,b][x,y]/ideal(x^2-a,y^2-b)

  assert(
    isFiniteOverCoefficients1 R1 == false and
    isFiniteOverCoefficients1 R2 == false and
    isFiniteOverCoefficients1 R3== false and
    isFiniteOverCoefficients1 R4== false and
    isFiniteOverCoefficients1 R5== true)
///

isFiniteOverCoefficientRing = method()
isFiniteOverCoefficientRing Ring := Boolean => (R) -> (
    if R.?NoetherInfo then return true;
    if not (try (coefficientRing R; true) else false) then return false;
    if not isAffineRing R then return false; 
    A := coefficientRing R;
    if not isField A and not isComputablePolynomialRing A then (
	    if debugLevel > 0 then << "expected a quotient of a polynomial ring over a field" << endl;
	    return false);
    if not isFiniteOverCoefficients1 R then (
        if debugLevel > 0 then << "ring is not finite over its coefficient ring" << endl;
        false
        )
    else true
    )    

checkNoetherNormalization = method()
checkNoetherNormalization RingMap := Boolean => (phi) -> (
    -- phi : A --> R
    -- check: 
    --   A is a polynomial ring over a field.
    --   phi(each var) is a linear form in R
    --   R is a quotient of a polynomial ring over the same field or over A.
    --   R is finite over A.
    )

checkNoetherNormalization Ring := Boolean => (B) -> (
    -- check that 
    --   B is a ring of the form A[x's]/I
    --   B is finite over A
    -- if so:
    --   set frac B? (using makeFrac)
    --   set NoetherInfo in B, frac B.
    if not isFiniteOverCoefficientRing B
    then error "ring is not in the proper form (set 'debugLevel>0' for details)";
    )

findComplement = method()
findComplement RingMap := phi -> (
    -- find a set of variables which is independent of the images of the variables under phi.
    -- assumption: phi(x) = affine linear function, for all variables x.
    )

makeFrac = method()
makeFrac Ring := Ring => (B) -> (
    if not isFiniteOverCoefficientRing B
    then error "expected the ring to be finite over the chosen polynomial ring";
    A := coefficientRing B; -- ASSUME: a polynomial ring over a field.
    KA := frac A;
    kk := coefficientRing A; -- must be a field, but not a fraction field.
    I := ideal B;
    ambientB := ring I;
    ambientKB := ((frac A)(monoid B)); -- TODO: does this handle degrees correctly?
    phiK := map(ambientKB,ambientB, vars ambientKB);
    JK := trim phiK I;
    KB := ambientKB / JK;
    B.frac = KB;
    KB.frac = KB;
    KB.isField = true;
    KB.baseRings = append(KB.baseRings, B);    
    BtoKB := map(KB,B,generators KB);
    inverse B := f -> 1_KB // BtoKB f;
    inverse KB := f -> 1 // f;
    fraction(B,B) := (f,g) -> (BtoKB f) * inverse g;
    fraction(KB,KB) := (f,g) -> f * inverse g;
    promote(B, KB) := (f,KB) -> BtoKB f;
    KA + B := (f,g) -> f + BtoKB g;
    B + KA := (f,g) -> BtoKB f + g;
    KA - B := (f,g) -> f - BtoKB g;
    B - KA := (f,g) -> BtoKB f - g;
    KA * B := (f,g) -> f * BtoKB g;
    B * KA := (f,g) -> BtoKB f * g;
    KA % B := (f,g) -> f % BtoKB g;
    B % KA := (f,g) -> BtoKB f % g;
    KA // B := (f,g) -> f // BtoKB g;
    B // KA := (f,g) -> BtoKB f // g;

    -- Now we consider factorization.  The plan is to factor (numerator and denominator if needed)
    -- over a polynomial ring, then bring back to B or KB
    (flattenedB, mapBtoFlattenedB) := flattenRing ambientB;
    S := ambient flattenedB; -- this is the polynomial ring where we will factor elements...
    mapBtofracS := map(frac S, B); -- TODO: does this do a 'sub'?
    mapKBtofracS := map(frac S, KB); -- TODO: does this do a 'sub'?
    StoB := map(B, S);
    numerator B := (f) -> StoB (numerator mapBtofracS f);
    numerator KB := (f) -> StoB (numerator mapKBtofracS f);
    denominator B := (f) -> lift(StoB denominator mapBtofracS f, A);
    denominator KB := (f) -> lift(StoB denominator mapKBtofracS f, A);
    factor KB := opts -> (f) -> hold numerator f/factor denominator f;
    expression KB := f -> expression numerator f / expression denominator f;
    setNoetherInfo(B, KB);
    setTraces KB;
    KB
    )

noetherForm = method(Options => {Remove => null, Variable => getSymbol "t"})
noetherForm RingMap := Ring => opts -> (f) -> (
    A := source f;
    R := target f;
    kk := coefficientRing R;
    if not isCommutative A then 
        error "expected source of ring map to be a commutative ring";
    if A === kk then return R;
    if not isAffineRing R then 
        error "expected an affine ring";
    if not isAffineRing A then 
        error "expected an affine ring";
    if not ( kk === coefficientRing A) then 
        error "expected polynomial rings over the same ring";
    gensk := generators(kk, CoefficientRing => ZZ);
    if not all(gensk, x -> promote(x,R) == f promote(x,A)) then 
        error "expected ring map to be identity on coefficient ring";

    ambientB := A[gens R, MonomialOrder => (monoid R).Options.MonomialOrder,
        Degrees => apply(degrees R, f.cache.DegreeMap)
        ]; 
    f' := map(ambientB, A, sub(f.matrix, ambientB));
    J1 := ideal for x in gens A list f' x - x; 
      -- todo: if opts.Remove, take lead terms of these (if they are linear?)
      -- reduce them (in ambient ring?)
      -- the lead terms which are variables in ambientB:
      --   create new ambientB' which leaves these variables out.
      -- then take J2 below, which should not involve the variables removed.
      --   perhaps check that.
      -- is the answer B = ambientB'/J2? (J2 after %J1, moving this to ambientB')
    J2 := sub(ideal R, vars ambientB);
    J2 = trim ideal((gens J2) % J1);
    B := ambientB/(J1 + J2);
    L := makeFrac B;
    B)

-*
noetherForm List := Ring => opts -> (xv) -> (
    -- R should be a quotient of a polynomial ring,
    -- xv a list of variables, algebraically independent in R
    -- result: a ring over the sub-poly ring or subfield generated by
    --  the variables xv.
    -- TODO: allow the xv to be linear forms, or even perhaps higher degree polynomials.
    --   for this part:
    --     make a polynomial ring A with #xv variables.
    --     make a ring map A --> (ring xv's), sending i-th var to xv#i.
    --     call noetherForm Ringmap.
    if #xv === 0 then error "expected non-empty list of variables";
    R := ring xv#0;
    if any(xv, x -> ring x =!= R) then error "expected variables all in the same ring";
    if any(xv, x -> index x === null) then error "expected variables";
    I := ideal R;
    Rambient := ring I;
    xindices := for x in xv list index x;
    otherindices := sort toList (set toList(0..numgens R - 1) - set xindices);
    kk := coefficientRing R;
    A := kk [xv, Degrees => (degrees R)_xindices, Join=>false];
    S := A[(gens R)_otherindices, Degrees => (degrees R)_otherindices, Join=>false];
    phi := map(S,Rambient, sub(vars Rambient, S));
    J := trim phi I;
    B := S/J;
    L := makeFrac B;
    B
    )
*-

noetherForm Ring := Ring => opts -> R -> (
    (F, J, xv) := noetherNormalization R;
    kk := coefficientRing R;
    t := opts.Variable;
    A := kk[t_0..t_(#xv-1)];
    phi := map(R,A,for x in xv list F^-1 x);
    noetherForm (phi, Remove => opts.Remove)
    )

-- version I'm working on 29 Sep 2020.
noetherForm List := Ring => opts -> (xv) -> (
    -- R should be a quotient of a polynomial ring,
    -- xv a list of algebraically independent polynomials in R
    -- result: a ring over the sub-poly ring or subfield generated by
    --  the xv.
    -- More detail:
    --   If {f0, ..., fr} are the algebraically indep polynomials.
    --   if any is a variable: use that name, remove from list of variables from ambientR
    --          has lead term which is a variable: use a variable t_i, but remove the var from the ambientR vars
    --          is a polynomial whose lead term is not linear: use a variable t_i.
    --   This function constructs a polynomial ring A, and with the remaining set of variables
    --      a quotient A[remaining vars]/I, isomorphic to R.
    
    -- TODO: allow the xv to be linear forms, or even perhaps higher degree polynomials.
    --   for this part:
    --     make a polynomial ring A with #xv variables.
    --     make a ring map A --> (ring xv's), sending i-th var to xv#i.
    --     call noetherForm Ringmap.
    if #xv === 0 then error "expected non-empty list of variables";
    R := ring xv#0;
    if any(xv, x -> ring x =!= R) then error "expected variables all in the same ring";
    I := ideal R;
    ambientR := ring I;
    gensR := new MutableList from gens ambientR;
    --gensA1 := select(xv, f -> index f =!= null); -- keep these in order.  Note that there should not be two the same.
    --if #gensA1 != #(unique gensA1) then error "cannot have same variable occuring twice";
    count := -1;
    -- this loop returns a list of {varname, value in R}, 
    -- and it also modifies gensR (sets any variable to null that should not be in gens of B).
    elems := for f in xv list (
        if index f =!= null then (
            gensR#(index f) = null;
            {f, f}
            )
        else (
            m := leadMonomial f;
            if index m =!= null then (
                gensR#(index m) = null;
                );
            count = count+1;
            {(opts.Variable)_count, f}
        ));
    keepList := select(toList gensR, x -> x =!= null);
    -- Create A and B' (ambient for the soon to be created B).
    A := (coefficientRing R)(monoid [elems/first]);
    B' := A(monoid [keepList, Join => false]);
    -- Now create B, and the isomorphism phi: B --> R
    phi' := map(R, B', keepList | (elems/last));
    J := trim ker phi';
    B := B'/J;
    phi := map(R, B, phi'.matrix);
    -- Now create the inverse of phi.  One should be able to do phi^-1, but fails (Sep 2020, 1.16)
    -- Here is a workaround for the moment.
    workAroundInverse phi; -- sets inverse of phi.
-*    
    (B'', F) := flattenRing B; -- B == source phi, R == target phi
    phi.cache.inverse = F^-1 * (phi * F^-1)^-1;
    phi.cache.inverse.cache.inverse = phi;
    assert(phi^-1 * phi === id_(source phi));
    assert(phi * phi^-1 === id_(target phi));
*-
    B.cache#"NoetherMap" = phi; -- TODO: where to put this.
    L := makeFrac B;
    B
    )

-- This workaround sets the inverse of the isomorphism phi, in the case
-- when the coefficient ring of source ring is not the coefficient ring of the target ring.
-- It is currently assumed, I think, that the target ring's coefficient ring is the
-- same as the coeff ring of the flattened ring of the source.
workAroundInverse = method()
workAroundInverse RingMap := (phi) -> (
    B := source phi;
    R := target phi;
    (B'', F) := flattenRing B;
    phi.cache.inverse = F^-1 * (phi * F^-1)^-1;
    phi.cache.inverse.cache.inverse = phi;
    --assert(phi^-1 * phi === id_B); -- TODO: make sure these are the same?  The matrices are different sometimes only with degrees.
    --assert(phi * phi^-1 === id_R); -- TODO: same
    )
///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
  -- working on noetherForm {list of polys"
  S = ZZ/101[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I

  use R; noetherForm {a,d}
  use R; noetherForm {a,d+c}
  use R; noetherForm {a+b,d+c}
  use R; B = noetherForm {a+b,a+d}
  use R; noetherForm {a^2, d^2}

  B1 = ZZ/101[a, b, c, d, t_0, t_1, MonomialOrder=>{4, 2}]
  ideal(t_0 - (a+b), t_1 - (a+d)) + sub(I, B1)
  see ideal gens gb oo    
  -- loop through the list, 
  -- make a variable name for each polynomial (for the coeff ring A)
  -- for each, say what the image is in R?
  -- also, if we are taking a variable name out of R, place it in a set?
  -- 
  -- 
  
  -- xv = {a, d+c}
  f1 = c+d
  A = ZZ/101[a, t]
  B' = A[b,d,Join=>false]
  use R
  phi = map(R, B', {b, d, a, f1})
  J = trim ker phi
  B = B'/J
  -- now we need the isomorphism
  phi' = map(R, B, phi.matrix)
  ker phi'
  
  -- here is one way to compute the inverse of phi'...
  -- this should not be required, this is a workaround
  (B'', F) = flattenRing source phi'
  phi'.cache.inverse = F^-1 * (phi' * F^-1)^-1
  phi'.cache.inverse.cache.inverse = phi'
  assert(phi'^-1 * phi' === id_B) 
  assert(phi' * phi'^-1 === id_R) 

  -- I will need to place the inverse of the ring F : map R --> B into F.cache.inverse (and vice versa)

  -- Create A, create B' (ambient)
  -- make a map phi'
  -- ker of it, then make a map phi.
  -- create its inverse.
  -- stash phi into B? or R?
///

beginDocumentation()

doc ///
  Key
    NoetherNormalForm
  Headline
    code for Noether normal forms of affine rings
  Description
    Text
///

doc ///
  Key
    noetherForm
    (noetherForm, List)
    (noetherForm, RingMap)
    (noetherForm, Ring)
  Headline
    place the target of a ring map into Noether normal form, via the map
  Usage
    B = noetherForm phi
    B = noetherForm xv
    B = noetherForm R
  Inputs
    phi:RingMap
      from a ring {\tt A} to a ring {\tt R}
    xv:List
      of variables in an affine ring {\tt R} over which {\tt R} is finite
    R:Ring
      an affine equidimensional and reduced ring
  Outputs
    B:Ring
      isomorphic to B, but of the form {\tt A[new variables]/(ideal)}.
  Consequences
    Item
      The following fields are set in {\tt R}:
    Item
      The following fields are set in {\tt B}:
    Item
      The following fields are set in {\tt L = frac B}:
  Description
    Text
    Example
      kk = ZZ/101
      A = kk[t]
      R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
      phi = map(R,A,{R_0})
      B = noetherForm phi
    Example
      kk = ZZ/101
      x = symbol x
      y = symbol y
      R = kk[x,y,z]/(ideal(x*y, x*z, y*z))
      A = kk[t]
      phi = map(R,A,{R_0+R_1+R_2})
      B = noetherForm phi
  Caveat
    The base field must currently be a finite field, or the rationals.
    Finiteness is not yet checked.
  SeeAlso
///

doc ///
  Key
    multiplication
    (multiplication, RingElement)
  Headline
    matrix of multiplication by an element
  Usage
    multiplication f
  Inputs
    f:RingElement
  Outputs
    :Matrix
  Description
    Text
      Given a ring.
  Caveat
    One must have created this ring with @TO noetherForm@.
  SeeAlso
    noetherForm
    (inNoetherForm, Ring)
    (getBasis, Ring)
///

doc ///
  Key
    traceForm
    (traceForm, Ring)
  Headline
    trace form matrix of ring created using noetherForm
  Usage
    traceForm R
  Inputs
    R:Ring
  Outputs
    :Matrix
  Description
    Text
  Caveat
    One must have created this ring with @TO noetherForm@.
  SeeAlso
    noetherForm
    (inNoetherForm, Ring)
    (getBasis, Ring)
    (multiplication, RingElement)
///

doc ///
  Key
    inNoetherForm
    (inNoetherForm, Ring)
  Headline
    whether the ring was created using noetherForm
  Usage
    inNoetherForm R
  Inputs
    R:Ring
  Outputs
    :Boolean
  Description
    Text
  Caveat
    This function only checks whether the ring was vreated using @TO noetherForm@, not
    whether it really is in Noether normal form
  SeeAlso
    noetherForm
///

doc ///
  Key
    getBasis
    (getBasis, Ring)
  Headline
    basis over coefficient ring of ring in Noether form
  Usage
    getBasis R
  Inputs
    R:Ring
  Outputs
    :Matrix
  Description
    Text
  Caveat
    One must have created this ring with @TO noetherForm@.
  SeeAlso
    noetherForm
    (inNoetherForm, Ring)
    (getBasis, Ring)
    (multiplication, RingElement)
///

TEST ///
  -- test-finiteOverCoefficientRing
-*
  restart
  needsPackage "NoetherNormalForm"
*-
  A = ZZ/101[t]  
  B = A[x,y]/(x^2-y*t, y^3)
  assert isFiniteOverCoefficientRing B

  debugLevel = 1
  A = ZZ/101
  B = A[x,y]/(x^2, y^3)
  assert isFiniteOverCoefficientRing B


  A = ZZ/101
  B = A[x,y]/(x^2, x*y)
  assert not isFiniteOverCoefficientRing B
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
  B = noetherForm {x}
  L = frac B
  describe B
  describe L
  getBasis B
  getBasis L
  multiplication B_0
  (getBasis B)/multiplication/trace
  (getBasis L)/multiplication/trace
  trace y
  trace multiplication y == trace y
  trace multiplication y_L == trace y_L
  M = multiplication y_L
  trace M
  trace(y_L)
  trace y
///

TEST ///
  -- of makeFrac
-*
  restart
  debug needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  A = kk[x];
  B = A[y, Join => false]/(y^4-x*y^3-(x^2+1)*y-x^6)
  L = makeFrac B
  describe L
  assert(degree y_L === {1})
  assert(monoid L === monoid B)
  --assert(isField L) -- not yet.
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
  
  test the following:
    1. singly graded case.
    2. inhomog case
    3. multi-graded case.  What to do if phi is not graded?
    4. subset of the variables
    5. a bunch of linear forms
    6. what else?
*-
  needsPackage "PushForward"
  kk = ZZ/101
  A = kk[t]
  x = symbol x
  y = symbol y
  R = kk[x,y]/(y^4-x*y^3-(x^2+1)*y-x^6)
  phi = map(R,A,{R_0})
  phi = map(R,A,{R_0^2})  
  B = noetherForm phi
  describe B
  L = frac B
  describe L
  getBasis B
  getBasis L

  multmaps = for x in getBasis B list pushFwd(map(B,A), map(B^1, B^1, {{x}}))
  multmaps2 = for x in getBasis B list multiplication x
-- TODO: should we try to insure that these matrices use the same bases?
--  assert(multmaps === multmaps2) -- NOT EQUAL.  pushFwd uses different basis for B?
--                                  -- would be nice: to have this play well with pushFwd... if possible.

  traces = multmaps/trace
  MB = pushFwd(map(B,A), B^1) -- dim 4, free
  map(A^1, MB, {traces}) -- traces as a map of modules
  
  use B
  1/x
  1/x^2
  1/y
  (1/y) * y == 1
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
  
  test the following:
    1. singly graded case.
    2. inhomog case
    3. multi-graded case.  What to do if phi is not graded?
    4. subset of the variables
    5. a bunch of linear forms
    6. what else?
*-
  S = QQ[a..d]
  I = ideal"a3-b2-c, bc-d, a2-b2-d2"
  R = S/I

  B = noetherForm R
  A = coefficientRing B  
  degrees B -- not good... multigradings!
  leadTerm ideal B

  

///

TEST ///      
-*
  restart
  needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  A = kk[s,t]
  S = kk[a..d]
  I = monomialCurveIdeal(S, {1,3,4})
  R = S/I
  phi = map(R,A,{R_0, R_3})
  B = noetherForm phi
  L = frac B
describe B
describe L
getBasis B
getBasis L
  multmaps = for x in getBasis L list multiplication x
  multmapsB = for x in getBasis B list multiplication x

  traces = multmaps/trace
  traces = multmapsB/trace

  traceForm L
-*
  -- pushFwd doesn't currently work if the coeff ring is a fraction field.
  needsPackage "PushForward"
  --multmaps2 = for x in getBasis L list pushFwd(map(L,frac A), map(L^1, L^1, {{x}}))
  --assert(multmaps === multmaps2)
  MB = pushFwd(map(B,A), B^1) -- dim 4, free
  map(A^1, MB, {traces}) -- traces as a map of modules
  ML = pushFwd(map(L,frac A), L^1) -- dim 4, free -- FAILS
  map(A^1, ML, {traces}) -- traces as a map of modules -- FAILS, since last line fails.
  traces = for x in flatten entries basis B list 
    trace pushFwd(map(B,A), map(B^1, B^1, {{x}}))
*-
  kk = ZZ/101
  R = kk[symbol x,y,z]/(x*y, x*z, y*z)
--  R = ZZ[symbol x,y,z]/(x*y, x*z, y*z)  --??
  A = kk[t]
  phi = map(R,A,{R_0+R_1+R_2})
  B = noetherForm phi
  L = frac B
  getBasis B
  getBasis L
  (getBasis L)/multiplication/trace
  traceForm L
///

-- WIP --
TEST ///
  -- test of creation of Noether normal form from a list of variables in a ring.
-*
  restart
  needsPackage "NoetherNormalForm"
*-

  S = QQ[a..d]
  R = S/monomialCurveIdeal(S,{1,3,4})
  B = noetherForm{a,d}
  frac B
  coefficientRing B
  coefficientRing frac B
  assert(coefficientRing frac B === frac coefficientRing B)
  assert(vars B == matrix"b,c")
  assert(numcols vars coefficientRing B == 2)
  -- going back and forth from R to B
  --   this works since we can do matching of variable names
  f = map(R, B)
  g = map(B, R)
  assert(f*g === id_R)
  assert(g*f === id_B)    

  -- Let's check some ring of elements
  A = coefficientRing B
  L = frac B
  assert(ring a === A)
  assert(ring b === L)
  use B
  assert(ring b === B)
  use frac A
  assert(ring a === frac A)

  use L
  gens(L, CoefficientRing => ZZ)
  assert(all(oo, v -> ring v === L))
  assert((1/b) * b == 1)
  assert((1/c) * c == 1)
  assert((1/(b+c)) * (b+c) == 1)
  assert(1/(a+b)*(a+b) == 1)
  assert (1/(b+c) * (b+c) == 1)

  h = 1/(b+c)
  factor h
  assert (denominator h == a^2*d - a*d^2)
  numerator h -- in the ring B
  assert(ring numerator h === B)
  assert(ring denominator h === A)
  
  getBasis B
  getBasis L

  multiplication b
  multiplication L_0
  traceForm L

  R = QQ[a..d]/(b^2-a, b*c-d)
  assert try (B = noetherForm{a,d}; false) else true  -- should give an error message
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
--  needsPackage "NoetherNormalization"
  kk = ZZ/101
  R = kk[x,y]/(x*y-1)
  B = noetherForm R
  describe B
  frac B
  A = kk[t]
  use R
  phi = map(R,A,{x+y})

  noetherForm phi
  noetherForm R
    
  (F, J, xv) = noetherNormalization R
  R' = (ambient R)/J

  G = map(R', R, sub(F.matrix, R'))
  isWellDefined G    
  G^-1 (xv_0)
  ideal R'
  ideal R
  for x in xv list G^-1 x
  A = kk[t]
  phi = map(R, A, for x in xv list G^-1 x)
  noetherForm phi
///

TEST ///
-*
  restart
  needsPackage "NoetherNormalForm"
*-
  kk = ZZ/101
  R = kk[a,b,c,d]
  I = ideal"a2,ab,cd,d2"
  S = reesAlgebra I
  S = first flattenRing S

  noetherForm({a - w_0,b,c,d,w_0 + w_1 + w_2 + w_3})  

  elapsedTime (F, J, xv) = noetherNormalization S -- wow, this takes more time than I would have thought! 3.1 sec on my macbookpro, Sep 2020.

  xv/(x -> F x)

  F (ideal S) == J  
  R' = (ambient S)/J  
  A = kk[t_0..t_(#xv-1)]
  
  phi = map(S,A, xv/(x -> F x))
  
  B = noetherForm phi
  L = frac B
  describe L
  
  isHomogeneous S -- true
  isHomogeneous R' -- false
  
  noetherForm S
///

end----------------------------------------------------------

restart
uninstallPackage "NoetherNormalForm"
restart
installPackage "NoetherNormalForm"
check NoetherNormalForm
restart
needsPackage  "NoetherNormalForm"

doc ///
  Key
  Headline
  Usage
  Inputs
  Outputs
  Description
    Text
    Example
  Caveat
  SeeAlso
///


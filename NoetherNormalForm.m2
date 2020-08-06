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
    "noetherForm",
    "makeFrac",
    "getBasis",
    "getBasisMatrix",
    "inNoetherForm",
    "multiplication",
    "traceForm",
    "tr",
    -- keys used:
    "noetherField",
    "noetherRing",
    "NoetherInfo",
    "Remove"
    }

raw = value Core#"private dictionary"#"raw"
rawIsField = value Core#"private dictionary"#"rawIsField"
isField EngineRing := R -> (R.?isField and R.isField) or rawIsField raw R

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

tr = method()
tr RingElement := (f) -> (
     -- R = ring f should be a noetherRing or noetherField
     -- result is in the coefficient ring of R.
     R := ring f;
     RK := noetherField R;
     NI := noetherInfo RK;
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
    NI := noetherInfo R;
    if not NI#?"trace form" then NI#"trace form" = (
        S := getBasis R;
        K := coefficientRing R;
        M := mutableMatrix(K, #S, #S);
        for i from 0 to #S-1 do
        for j from i to #S-1 do (
            f := tr(S#i * S#j);
            M_(i,j) = M_(j,i) = f;
            );
        matrix M
        );
    NI#"trace form"
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

findComplement = method()
findComplement RingMap := phi -> (
    -- find a set of variables which is independent of the images of the variables under phi.
    -- assumption: phi(x) = affine linear function, for all variables x.
    )

makeFrac = method()
makeFrac Ring := Ring => (B) -> (
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
    J2 := sub(ideal R, vars ambientB);
    J2 = trim ideal((gens J2) % J1);
    B := ambientB/(J1 + J2);
    L := makeFrac B;
    B)

noetherForm List := Ring => opts -> (xv) -> (
    -- R should be a quotient of a polynomial ring,
    -- xv a list of variables, algebraically independent in R
    -- result: a ring over the sub-poly ring or subfield generated by
    --  the variables xv.
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

noetherForm Ring := Ring => opts -> R -> (
    (F, J, xv) := noetherNormalization R;
    kk := coefficientRing R;
    t := opts.Variable;
    A := kk[t_0..t_(#xv-1)];
    phi := map(R,A,for x in xv list F^-1 x);
    noetherForm (phi, Remove => opts.Remove)
    )


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
    Finiteness is not yet checked.  The 3rd version is not yet written.
  SeeAlso
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
  tr y
  trace multiplication y == tr y
  trace multiplication y_L == tr y_L
  M = multiplication y_L
  trace M
  tr(y_L)
  tr y
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
  assert(multmaps === multmaps2)

  traces = multmaps/trace
  MB = pushFwd(map(B,A), B^1) -- dim 4, free
  map(A^1, MB, {traces}) -- traces as a map of modules
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
  B = noetherForm{a,d} -- needs to give an error! BUG need to check that it is finite...
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
  phi = map(R,A,{x+y})
  noetherForm phi

  --noetherForm R  -- call noetherNormalization, to find the linear forms that are independent.
    
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
  
  elapsedTime (F, J, xv) = noetherNormalization S -- wow, this takes more time than I would have thought!

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


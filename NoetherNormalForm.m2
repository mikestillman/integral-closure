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
    "multiplication",
    "traceForm",
    "tr",
    -- keys used:
    "noetherField",
    "noetherRing",
    "NoetherInfo"
    }

-- private routine
setNoetherInfo = method()
setNoetherInfo(Ring, Ring) := (B, KB) -> (
    B.NoetherInfo = new MutableHashTable;
    KB.NoetherInfo = new MutableHashTable;
    B.NoetherInfo#"noetherField" = KB;
    KB.NoetherInfo#"noetherRing" = B;
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
    NI := noetherInfo R;
    if not NI#?"basis" then (
        -- assumption: R is finite over the coefficient ring
        -- returns a matrix over R whose entries are generators
        -- of R over the coeff ring
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
    H#"traces"
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
makeFrac Ring := (B) -> (
    A := coefficientRing B;
    I := ideal B;
    ambientL := ((frac A)(monoid B));
    L := ambientL / sub(I, vars ambientL);
    B.frac = L; -- TODO: also add in promotion/lift functions?
    L.frac = L; -- I wonder if we need to set KB to be a field too?
    L
    )

noetherForm = method()
noetherForm RingMap := Ring => (f) -> (
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
    setNoetherInfo(B, L);
    setTraces L;
    B)

noetherForm List := (xv) -> (
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
     KA := frac A;
     SProd := kk(monoid[(gens R)_otherindices, xv, 
             MonomialOrder => {#otherindices, #xv}, 
             Degrees=>join((degrees R)_otherindices, (degrees R)_xindices)]);
     S := A[(gens R)_otherindices, Degrees => (degrees R)_otherindices, Join=>false];
     SK := KA[(gens R)_otherindices, Degrees => (degrees R)_otherindices, Join=>false];
     phi := map(S,Rambient, sub(vars Rambient, S));
     phiK := map(SK,Rambient, sub(vars Rambient, SK));
     J := trim phi I;
     JK := trim phiK I;
     B := S/J;
     KB := SK/JK;
     BtoKB := map(KB,B,generators KB);
     inverse B := f -> 1_KB // BtoKB f;
     B / A := (f,g) -> (1/g) * BtoKB f;
     B / B := (f,g) -> (BtoKB f) * (inverse g);
     KB / A := (f,g) -> (1/g) * f;
     mapBtofracSProd := map(frac SProd, B);
     mapKBtofracSProd := map(frac SProd, KB);
     SProdToB := map(B, SProd);
     SProdToS := map(S, SProd);
     numerator B := (f) -> SProdToB (numerator mapBtofracSProd f);
     numerator KB := (f) -> SProdToB (numerator mapKBtofracSProd f);
     denominator B := (f) -> lift(SProdToB denominator mapBtofracSProd f, A);
     denominator KB := (f) -> lift(SProdToB denominator mapKBtofracSProd f, A);
     -- net KB := (f) -> (
     --     n := numerator f; 
     --     d := denominator f;
	 --     resultDenom := if d == 1 then 1 else factor d;
	 --     (hold n) / resultDenom
     --     );
     factor B := opts -> (f) -> (hold factor (numerator mapBtofracSProd f))/(factor denominator f);
     factor KB := opts -> (f) -> (hold factor (numerator mapKBtofracSProd f))/(factor denominator f);
     B.frac = KB; -- TODO: also add in promotion/lift functions?
     KB.frac = KB; -- I wonder if we need to set KB to be a field too?  If so, that might be a problem...
     KB.isField = true;
     setNoetherInfo(B, KB);
     setTraces KB;
     B)

--noetherForm RingMap := Ring => (phi) -> (
    -- input: a ring map phi : A --> R, where
    --   A is a polynomial ring
    --   R is finite over A, a quotient of a polynomial ring over a field (which is not a fraction field, currently)
    -- output:
    --   B is a polynomial ring with coefficient ring A.
    -- consequences:
    --   R.cache#"NoetherForm" is set to B, or is it set to the pair of isomorphisms R --> B, B --> R?
    --   B.cache#"NoetherRing" is set to B
    --   B.cache#"NoetherField" is set to L = frac B (but this frac is (frac A)[newvars]/I)
    --   L.cache#"NoetherRing" is set to B
    --   L.cache#"NoetherField" is set to L.
    --   what else is set?  We also create:
    --     B as an A-module
    --     L as an K-module (K = frac A).
    --     trace : L --> frac A
    --     trace : B --> A
    --     multiplication maps?
    --     trace form itself?
    -- Step 1.  Check that phi is gives a NNF.
    -- Step 2.  Create B, unless R is already of the form A[vars]/I, finite over A.
    -- Step 3.  Create frac B.
    -- Step 4.  Create the modules over A, K.
    -- Step 5.  Create the trace maps
    -- Step 6.  What else to make
--    )


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
  Headline
    place the target of a ring map into Noether normal form, via the map
  Usage
    B = noetherForm phi
  Inputs
    phi:RingMap
      from a ring {\tt A} to a ring {\tt R}
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
  B = noetherForm phi
  L = frac B
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
  A = kk[t]
  phi = map(R,A,{R_0+R_1+R_2})
  B = noetherForm phi
  L = frac B
  getBasis B
  getBasis L
  (getBasis L)/multiplication/trace
  traceForm L
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

  gens(L, CoefficientRing => ZZ)
  assert(all(oo, v -> ring v === L))
  assert((1//L_0) * L_0 == 1) -- BUG: would like 1/L_0 to work here...
  assert((1//L_1) * L_1 == 1)
  assert((1//(L_0+L_1)) * (L_0 + L_1) == 1)
  (1//(L_0 + L_1)) * (b+c) == 1 -- FAILS: * is not defined for L * B ?

  h = 1//(L_0 + L_1)
  factor h
  denominator h == a^2*d - a*d^2 -- ?? these are in different rings??? But this is true...
  numerator h -- in the ring B
  
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
  needsPackage "NoetherNormalization"
  kk = ZZ/101
  R = kk[x,y]/(x*y-1)
  A = kk[t]
  phi = map(R,A,{x+y})
  noetherForm phi

  noetherForm R  -- call noetherNormalization, to find the linear forms that are independent.
    -- 
    
  (F, J, xv) = noetherNormalization R
  R' = (ambient R)/J

  G = map(R', R, sub(F.matrix, R'))
  isWellDefined G    
  
  ideal R'
  ideal R
  for x in xv list G^-1 x
  A = kk[t]
  phi = map(R, A, for x in xv list G^-1 x)
  noetherForm phi
  
  F^-1 ((target 
///

-- A list of things to add to M2 for the next release.

-- MES TODO: put these 2 functions into the Core
-- MES TODO: list of lists of degrees: output an ideal.
-*
random(ZZ,Ideal) := RingElement => opts -> (d,J) -> random({d},J,opts)
random(List,Ideal) := RingElement => opts -> (d,J) -> ( -- MES TODO: fix this function, place into the core.
     R := ring J;
     B := basis(d,J);
     (super(B * random(source B, R^(-d), opts)))_(0,0)
     )
*-
   

-- From integralClosure...

-- -- Test of icFractions
///
-*
  restart
*-
  S = QQ [(symbol Y)_1, (symbol Y)_2, (symbol Y)_3, (symbol Y)_4, symbol x, symbol y, Degrees => {{7, 1}, {5, 1}, {6, 1}, {6, 1}, {1, 0}, {1, 0}}, MonomialOrder => ProductOrder {4, 2}]
  J = ideal(Y_3*y-Y_2*x^2,Y_3*x-Y_4*y,Y_1*x^3-Y_2*y^5,Y_3^2-Y_2*Y_4*x,Y_1*Y_4-Y_2^2*y^3)
  T = S/J       
  assert(icFractions T == 
      flatten entries substitute(
          matrix {{(Y_2*y^2)/x, (Y_1*x)/y, Y_1, Y_2, Y_3, Y_4, x, y}}, frac T))
  -- MES: but notice: the displayed fractions are not these!
///


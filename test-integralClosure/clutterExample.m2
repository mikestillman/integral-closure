
idealInSingLocus Ring := Ideal => opts -> S -> (
     -- Input: ring S = S'/I, where S' is a flattened poly ring.
     --  Verbosity: if >0 display timing
     --  Strategy: List. If isMember(StartWithOneMinor, opts.Strategy) then 
     -- Output:
     --        ideal in non-normal locus
     -- private subroutine of integralClosure

     if opts.Verbosity >= 1 then (
	  << " [jacobian time " << flush;
	  );
     if member(StartWithOneMinor, opts.Strategy) then 
          t1 := timing (J := ideal nonzeroMinor(codim ideal S, jacobian S))
     else
          t1 = timing (J = minors(codim ideal S, jacobian S));

     if opts.Verbosity >= 1 then (
        << t1#0 << " sec #minors " << numgens J << "]" << endl;
	);
     J
     )




end--
restart
debug needsPackage "FastLinAlg"
debug needsPackage "IntegralClosure"
load "clutterExample.m2"
p=2;q=4
Q = toList(0..q-1)
ss = subsets (Q,p)
small = sum toList(0..p-1)
big = sum toList(q-p..q-1)
L = for s from small to big list select(ss, t -> sum t == s)
apply(L,ell -> (sum (ell_0), #ell))
tally (L/length)
flatten select(L, ell -> #ell == 5)


kk = ZZ/32003 
S = kk[x_(0,0)..x_(p-1,q-1)]
M = transpose genericMatrix(S,x_(0,0), q,p)
--I = minors(p,M);
--J = ideal apply(L, ell -> sum apply(ell, e -> det(M_e)));

I' = ideal apply(ss, s-> product(apply(p,i->x_(i,s_i))))
J' = ideal apply(L, ell-> sum(apply(ell, s->product(apply(p,i->x_(i,s_i))))))
elapsedTime integralClosure(J', J'_0, Verbosity => 2) --16 sec (in Zoom)
oo==I'

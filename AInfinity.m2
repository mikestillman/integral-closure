newPackage(
	"AInfinity",
    	Version => "0.1", 
    	Date => "October 4, 2020",
        Authors => {{Name => "David Eisenbud", 
                  Email => "de@msri.org", 
                  HomePage => "http://www.msri.org/~de"},
	          {Name => "Mike Stillman", 
                  Email => "mike@math.cornell.edu", 
                  HomePage => "http://pi.math.cornell.edu/~mike"}},
        Headline => "Compute AInfinity structures on free resolutions",
        DebuggingMode => true
    	)

export {
    "singleDegTP",
    "singleDegTripleTP"
    }
    
---Jesse Burke's code

-- assuming both A and B are in nonnegative degrees
-- returns a direct sum with keys indexed by i
-- the value at key i is A_i \otimes B_{n-i},
-- where n is the degree computed
singleDegTP = method();
singleDegTP(GradedModule, GradedModule, ZZ) := (A, B, n) -> (
    	directSum(apply(0..n, i -> (A_i ** B_(n-i))))
    )

-* The following code is broken, and isn't used anyway.
singleDegTP(Sequence, Ring, ZZ) := (modSeq, S, n) -> (
    if( n - (length modSeq) < 2)
     then directSum(apply(1..n), i -> prune coker map( S^1, S^1, 1))

     else directSum(splice(
	    apply( 2..(n-(length modSeq)), i -> (
    	    -- the right hand side, missing first component
	    R := singleDegTP(drop(modSeq, 1), S, n-i);
	    apply( indices R, seq -> (		    
		    prepend(i,seq) => ((modSeq#0)_i ** (source R_[seq]))))
	    ))
	))
)


singleDegTripleTP = method();
singleDegTripleTP(GradedModule, GradedModule, GradedModule, ZZ) := (A, B, C, n) -> (
    directSum( deepSplice(apply(0..n, i -> apply(0..(n-i), j -> (
		(i,j,n-i-j) => A_i ** (B_j ** C_(n-i-j)))))))
)
*-
-- assuming A, B, C are graded modules in nonnegative degrees
-- returns a direct sum with keys indexed by (i,j)
-- the value at key (i,j) is A_i \otimes (B_j \otimes C_(n-i-j)),
-- where n is the degree computed

--the following is the same as the preceding, but uses a smaller range of i,j, 
--appropriate since in the application A == B start in degree 2, 
--while G == C starts in degree 0

singleDegTripleTP = method()
singleDegTripleTP(GradedModule, GradedModule, GradedModule, ZZ) := (A, B, C, n) -> (
    directSum( deepSplice(apply(2..n-4, i -> apply(2..(n-i-2), j -> (
		(i,j,n-i-j) => A_i ** (B_j ** C_(n-i-j)))))))
)

aInfinity = method()
aInfinity(Ring, Module) := HashTable => (R,M) -> (
    --R should be a factor ring of S
    --M an R-module
    --The HashTable returned contains the A-infinity structures on 
    --S-free resolutions A of R and G of M up to stage n.
    --CAVEAT: for the moment we only compute 
    --m1,m2,m3 and  mG1,mG2,mG3.
Ai := new MutableHashTable;
S := ring presentation R;
RS := map(R,S);
A := res coker presentation R;
B := chainComplex(apply(length A-1, i-> A.dd_(i+2)))[-2];
G := res pushForward(RS,M);

m1 := symbol m1;
  apply(length B , i-> Ai#(m1_(i+3)) = B.dd_(i+3));

mG1 := symbol mG1;
  apply(length G , i-> Ai#(mG1_(i+1)) = G.dd_(i+1));    

m2 := symbol m2;    
  A0 := (chainComplex gradedModule (S^1))[-2];
  d := map(A0, B, i-> if (i == 2) then A.dd_1 else 0);
  N := nullhomotopy (d**id_B-id_B**d);
  apply(length B, i-> Ai#(m2_(i+4)) = N_(i+4));

mG2 := symbol mG2;        
  NG := nullhomotopy(d**G);
  apply(length G, i-> Ai#(mG2_(i+2)) = NG_(i+2));

mG3 := symbol mG3;
  sour = directSum components (source Ai#(mG2_3));
  Ai#(mG2_3) = map(G_2, sour, matrix Ai#(mG2_3));
  toLift =  map(G_2, B_2**B_2**G_0, 
  #(mG2_3)*(source Ai#(mG2_3))_[1]*(Ai#(m2_4)**id_(G_0))*t^-1 --m2(m2**1)
  #(mG2_3)*(source Ai#(mG2_3))_[0]*(id_(B_2)**Ai#(mG2_2)) --m2(1**m2)
             );
  Ai#(mG3_4) := toLift//(Ai#(mG1_3));
hashTable pairs Ai
)

    
-*   
phi = extend(A, A**A, map (A_0,A_0**A_0, id_(A_0)))

betti source N
betti target N
map(B,(B**B),N[2])

betti res G
N[2]
    alpha := map(A0,B_2**B_2, d**id_B-id_B**d)


F = map(A0,sAplus, i -> if (i == 2) then A.dd_1 else 0);
g2 = (F ** id_(sAplus) - id_(sAplus) ** F);
m2 = nullhomotopy g2;
	
	)    
*-  

///
restart
needsPackage "Complexes"
loadPackage("AInfinity",Reload => true)
S = ZZ/101[x,y,z]
R = S/(ideal gens S)^2
M = coker vars R


X = koszul matrix{{x^2,y^3}}
Y = koszul matrix{{y^5,z^7}}
components((X**Y)_2)
X_0**Y_1 ++ X_1**Y_0 == (X**Y)_1
betti oo
betti X

///

beginDocumentation()

doc ///
Key
  AInfinity
Headline
  Compute the A-infinity structures on free resolutions
Description
  Text
   Following Burke's paper "Higher Homotopies and Golod Rings":
   Given an S-free resolution A -> R = S/I, set B = A_+[1] (so that B_m = A_(m-1) for m >= 2, B_i = 0 for i<2),
   and alternate differentials have changed sign.
   
   The A-infinity structure  is a sequence of degree -1 maps m_n: B^(**n) \to B such that
   m_1 is the differential, 
   m2 is the multiplication (which is a homotopy B**B \to B lifting the degree -2 map
   d**1 - 1**d: B_2**B_2 \to B_1 (which induces 0)
       
   m_n for n>2 is a homotopy for the negative of the sum of degree -2 maps of the form
   m_(n-i+1)(1**...** 1 ** m_i ** 1 **..**),
   with inserting m_i into each possible (consecutive) sub product, and i = 2...n-1.
   Here m_1 represents the differential both of B and of B^(**n).
  Example
   I = Grassmannian(1,5, CoefficientRing => ZZ/32003); numgens(I)
   S = ring(I)
   M = S^1/I
   R = S/I
   
   A = res M; betti A
   B = (chainComplex apply(length A - 1, i -> -A.dd_(i+2)))[-2];
   
  Text
   We can compute the multiplication map on B as a homotopy:
  Example   
   A0 = (chainComplex gradedModule (S^1))[-2];
   F = map(A0,B, i -> if (i == 2) then A.dd_1 else 0);
   g2 = (F ** id_B - id_B ** F);
   m2 = nullhomotopy g2;
   betti source m2
   betti target m2
  Text
   Next we compute m_3:
  Example
   P = singleDegTripleTP(B, B, B, 8);
   BtB5 = singleDegTP(B, B, 5);
   BtB4 = singleDegTP(B, B, 4);
   t = tensorAssociativity(B_2, B_2, B_2);
   b = betti B
   a1 = BtB5_[3] * map(source BtB5_[3], source t, (m2#4 ** id_(B_2)) * (BtB4_[2] **
       id_(B_2)) * t);
   a2 = BtB5_[2] * map(source BtB5_[2], source t, (id_(B_2) ** (m2#4)) * (id_(B_2) **
       BtB4_[2]));
   a = m2#5 * (a1 + a2);
   m3 = a // B.dd_5;
   prune coker m3
   betti m3
SeeAlso
///

-*
restart
load("AInfinity.m2", Reload => true)
*-

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///



end--

restart
needsPackage "Complexes"
loadPackage("AInfinity", Reload =>true)
installPackage "AInfinity"


----------------------------------------
-- following is an example
n = 6
S = ZZ/32003[x_0..x_n]

-- makes the presentation matrix
M = matrix(apply( splice{0..(n-1)}, i -> {x_i, x_(i+1)}))

I = minors(2,M)
A = res I
betti A
----------------------------------------

-- input: chain complex A, assumed to be in nonnegative degrees
-- (the following is not a function, but it should be)

--e = max B

-- split A into two pieces
sAplus = (chainComplex apply(length A - 1, i -> -A.dd_(i+2)))[-2];
A0 = (chainComplex gradedModule (S^1))[-2];

-- shorthand
B = sAplus
--e = max B 
e = 6

temphhA1 = new HashTable from apply(toList(3..e), i -> (i => B.dd_i));
hhA = new HashTable from {1 => temphhA1};

-- calculate m2, by lift b`ing the multiplication map on R \otimes R \to R to A,
-- where R = S/I (quick check that what is below is equivalent to such a lifting)

F = map(A0,sAplus, i -> if (i == 2) then A.dd_1 else 0);
g2 = (F ** id_(sAplus) - id_(sAplus) ** F);
m2 = nullhomotopy g2;
class(m2)
source m2



P = singleDegTripleTP(B, B, B, 8);
BtB5 = singleDegTP(B, B, 5);
BtB4 = singleDegTP(B, B, 4);

t = tensorAssociativity(B_2, B_2, B_2);

-- can make following more clear by defining the matrices seperately and doing one call to 'map'
a1 = BtB5_[3] * map(source BtB5_[3], source t, (m2#4 ** id_(B_2)) * (BtB4_[2] **
	id_(B_2)) * t);
a2 = BtB5_[2] * map(source BtB5_[2], source t, (id_(B_2) ** (m2#4)) * (id_(B_2)
	** BtB4_[2]));
a = m2#5 * (a1 + a2);
m3 = a // B.dd_5;
betti m3
betti sAplus
----------------------------------------


betti source m2


indices 0
w = directSum(prune coker map( S^1, S^1, 1))
indices w
length (P,P,P)
class (P,P,P)
test = singleDegTP((B, B, B), S, 8);


betti ((B,B,B)#0)_4
components BtB5
BtB5^[1]

BtB5^[6]
class BtB5
indices BtB5

B = sAplus
P = singleDegTripleTP(B, B, B, 8);
BtB5 = singleDegTP(B, B, 5);
BtB4 = singleDegTP(B, B, 4);


t = tensorAssociativity(B_2, B_2, B_2);
b = betti B
b ** b
(b ** b) ** b 
((b ** b) ** b ) ** b

a1 = (id_(B_2) ** (m2#4)) * (id_(B_2) ** BtB4_[2]);
a2 = (m2#4 ** id_(B_2)) * (BtB4_[2] ** id_(B_2)) * t;



betti source m3
betti target m3
prune coker m3

b = betti B
b ** (b ** b)

prune (coker m3)
help prune
help rank
rank(m3 ** id_k)
m = m3 ** id_k;
class ker m
rank ker m
m

n = matrix{{1,1},{1,0}}
rank n
rank m
m === 0
betti source m
betti target m
target m3 === source (B.dd_5)
betti (source B.dd_5)
betti target m    
target m3
betti oo
betti (target m)
rank m3
m3


------tensor associativity
restart
S = ZZ/101[x,y]
K = koszul matrix{{x^2,y^3}}
assert(K**K**K != K**(K**K))
assert(K**K**K == (K**K)**K)
apply(length (K**K**K), i->((K**K)**K).dd_(i+1) - (K**(K**K)).dd_(i+1))
--tensorAssociativity(1,2,3):1(23)->(12)3

assert(K**K**K**K ==((K**K)**K)**K)
--1(2(3(4))) -> 1(2,3)4 -> (1,2)3)4 = 1234

for resolutions A of R, G of M, both length 3 , there is one nonzero component of m_3:
mG_3: B_2**B_2**G_0 ->G_3 == -mG_2(mB_2(B_2,B_2),G_0)-mG_2(B_2, mG_2(B_2,G_0))


1(2(3))->(1,2)3
1(2(3(4))) -> 1(2,3)4->(1,2)3)4
1(2(3

--why doesn't this work??

tensor List := Module => mods -> (
    if #mods == 1 then return mods_0;
    if #mods == 2 then return tensor(mods_0,mods_1);
    mods' := drop(mods,1);
    tensor(mods_0,tensor mods')
    )
mods = {S^2,S^3,S^4}
mods = {S^2,S^3}
tensor mods
tensor{S^2}

associativity = method()
associativity(List, List) := Matrix => blocks, mods -> (
-*
    blocks = {a,b,..,c} positive integers, 
    mods = {A_1,..,C_c}
    returns the map
    (A_1**..**A_a)**(B_1**..**B_b)**..**(C_1**..**C_c) -> A_1**..**C_c.
    Note that the built-in tensor product of multiple factors
    goes from left to right:
    tensorAssociativity: A*(B*C) -> A*B*C = (A*B)*C; 
*- 
    n := sum blocks;
   if blocks == {n-1,1} then tensorAssociativity(mods_0**;
   



-- assuming both A and B are in nonnegative degrees
-- returns a direct sum with keys indexed by i
-- the value at key i is A_i \otimes B_{n-i},
-- where n is the degree computed
singleDegTP = method();
singleDegTP(GradedModule, GradedModule, ZZ) := (A, B, n) -> (
    	directSum(apply(0..n, i -> (A_i ** B_(n-i))))
    )

-- assuming A, B, C are in nonnegative degrees
-- returns a direct sum with keys indexed by (i,j)
-- the value at key (i,j) is A_i \otimes (B_j \otimes C_(n-i-j)),
-- where n is the degree computed
singleDegTripleTP = method();
singleDegTripleTP(GradedModule, GradedModule, GradedModule, ZZ) := (A, B, C, n) -> (
    directSum( deepSplice(apply(0..n, i -> apply(0..(n-i), j -> (
		(i,j,n-i-j) => A_i ** (B_j ** C_(n-i-j)))))))
)

end--

restart
needsPackage "Complexes"
load "AInfinity.m2"

S = ZZ/101[a..d]
I = ideal"a,b"
C = complex koszul gens I
peek koszul gens I
peek complex koszul gens I

C21 = (C**C)**C
C12 = C**(C**C)
C21 == C12
C12.dd_2 == C12.dd_2
apply(length C21, i-> C12.dd_i == C21.dd_i)

--debug Core
--path = append(path, "/Users/math/Dropbox/Programming/M2/aInfinity")

--loadPackage "HigherHomotopiesOnResolution"


----------------------------------------
-- following is example
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


-- copy all of the above for a different example:

restart
load "AInfinity.m2"

I = Grassmannian(1,5, CoefficientRing => ZZ/32003); numgens(I)
S = ring(I)
M = coker gens I

R = S/I
k = coker vars R
-- F = res( k, DegreeLimit => 1)

A = res M; betti A

sAplus = (chainComplex apply(length A - 1, i -> -A.dd_(i+2)))[-2];
A0 = (chainComplex gradedModule (S^1))[-2];
F = map(A0,sAplus, i -> if (i == 2) then A.dd_1 else 0);
g2 = (F ** id_(sAplus) - id_(sAplus) ** F);
m2 = nullhomotopy g2;
betti source m2
betti target m2


B = sAplus
P = singleDegTripleTP(B, B, B, 8);
BtB5 = singleDegTP(B, B, 5);
BtB4 = singleDegTP(B, B, 4);

t = tensorAssociativity(B_2, B_2, B_2);
b = betti B

a1 = BtB5_[3] * map(source BtB5_[3], source t, (m2#4 ** id_(B_2)) * (BtB4_[2] **
	id_(B_2)) * t);
a2 = BtB5_[2] * map(source BtB5_[2], source t, (id_(B_2) ** (m2#4)) * (id_(B_2)
	** BtB4_[2]));
a = m2#5 * (a1 + a2);
m3 = a // B.dd_5;
prune coker m3
betti m3
----------------------------------------






betti source m2


-- assuming both A and B are in nonnegative degrees
-- returns a direct sum with keys indexed by i
-- the value at key i is A_i \otimes B_{n-i},
-- where n is the degree computed
singleDegTP = method();
singleDegTP(GradedModule, GradedModule, ZZ) := (A, B, n) -> (
    	directSum(apply(0..n, i -> (A_i ** B_(n-i))))
    )

-- assuming A, B, C are in nonnegative degrees
-- returns a direct sum with keys indexed by (i,j)
-- the value at key (i,j) is A_i \otimes (B_j \otimes C_(n-i-j)),
-- where n is the degree computed
singleDegTripleTP = method();
singleDegTripleTP(GradedModule, GradedModule, GradedModule, ZZ) := (A, B, C, n) -> (
    directSum( deepSplice(apply(0..n, i -> apply(0..(n-i), j -> (
		(i,j,n-i-j) => A_i ** (B_j ** C_(n-i-j)))))))
)

singleDegTripleTP(GradedModule, GradedModule, GradedModule, ZZ) := (A, B, C, n) -> (
    directSum( deepSplice(apply(2..n-4, i -> apply(2..(n-i-2), j -> (
		(i,j,n-i-j) => A_i ** (B_j ** C_(n-i-j)))))))
)

singleDegTP = method();
singleDegTP(Sequence, Ring, ZZ) := (modSeq, S, n) -> (
    if( n - (length modSeq) < 2) then 
        directSum(apply(1..n, 0) => prune coker map( S^1, S^1, 1))
    else directSum(splice(apply( 2..(n-(length modSeq)), i -> (
    	    -- the right hand side, missing first component
	    R = singleDegTP(drop(modSeq, 1), S, n-i);
	    apply( indices R, seq -> (		    
		    prepend(i,seq) => ((modSeq#0)_i ** (source R_[seq])))))))))

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

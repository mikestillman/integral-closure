restart

tensorList = method()
tensorList List := L -> (
    --L = {C_0..C_(p-1)}, list of modules or chain complexes. Form the tensor product of the C_i
    --in such a way that if the tensor products of the modules (C_i)_m are labeled,
    --then the modules of the tensor product are direct sums of modules from the hashtable, so that
    --componentsAndIndices applied to pC gives the correct list of indices, and
    --thus picture pC.dd_m works.
    S := ring L_0;
    if #L == 0 then error "needs list of length > 0";
    if #L == 1 then return L_0;
    if #L > 1 and class(L_0) === Module then return tensorList(drop(L, -1)) ** last L;
    p := #L;
    Min := apply(L, C->min C);
    Max := apply(L, C->max C-1);
    pCModules := apply(#L + sum Max - sum Min, i ->(
	    d := i+sum Min;
	    com := select(compositions(p,d), c -> all(p, i->Min_i <= c_i and c_i<= Max_i) and c != {});
	    print com;
    	    t := apply(com, co -> (co => tensorList(apply(p, pp->(L_pp)_(co_pp)))));
	    select(t, tt-> #tt != 0)
	    ))
    --make the differential as a block matrix:
--    chainComplex(apply #pCModules, i->map(pCModules_i, pCModules_(i+1), (p,q) -> matrix ****))
    )


kk = ZZ/101
S = kk[a,b,c]
R1 = S^1/ideal(a,b)
A = res R1
t = tensorList{A,A}
class (last t)
#last t
last t
t0=select(t, tt -> #tt !=0) -- note that this line is the same as the last line of the function!
--Why doesn't this line work when it's inside the function, but does when it's outside??
last t0

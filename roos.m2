roosNonKoszul = method()
roosNonKoszul ZZ := (n) -> (
    S := ZZ/32003[a,b,c,d,e,f];
    I1 := ideal"a2,ab,bc,c2,cd,d2,de,ef,f2";
    I2 := ideal(a*c + n*c*f - d*f);
    I3 := ideal(c*f + a*d + (n-2) * d*f);
    I := I1 + I2 + I3;
    (I, S/I)
    )

roosNonKoszul QQ := (n) -> (
    S := QQ[a,b,c,d,e,f];
    I1 := ideal"a2,ab,bc,c2,cd,d2,de,ef,f2";
    I2 := ideal(a*c + n*c*f - d*f);
    I3 := ideal(c*f + a*d + (n-2) * d*f);
    I := I1 + I2 + I3;
    (I, S/I)
    )

end--
restart
load "roos.m2"
(I,R) = roosNonKoszul 3
betti res I
betti res coker vars R

(I,R) = roosNonKoszul 4
betti res I
betti res(coker vars R, LengthLimit=>5)

(I,R) = roosNonKoszul 5
betti res I
betti res(coker vars R, LengthLimit=>5)

for n from 2 to 8 list betti res first roosNonKoszul n

for n from 2 to 8 list elapsedTime print betti res(coker vars last roosNonKoszul n, LengthLimit=>n+1)

(I,R) = roosNonKoszul (1/2)
betti res I
betti res(coker vars R, LengthLimit=>5)
betti res(coker vars R, LengthLimit=>10, DegreeLimit=>2)


-- Another Roos non-Koszul example (but check that!).  Does this fit into a family like the
-- ones above?
S = ZZ/32003[a,b,c,d,e,f];
I = ideal"a2,b2,c2,d2,e2,f2,ab,bc,de,ef,ac+3cd-df,cf+ad+df"

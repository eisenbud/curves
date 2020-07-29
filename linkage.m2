S = ZZ/101[a,b,c,d]
I = monomialCurveIdeal(S,{1,2,3})
f1 = ideal a
f2 = ideal I_0
I' = f1*I+f2
g = f1*ideal I_2
J = (f1*g+f2):I
IJ = intersect(I,J)
g' = trim ideal((gens IJ) % f2)
I'J = intersect (I', J)
gens 
gens f2 % intersect(I,J)
betti res (f1*I+f2)

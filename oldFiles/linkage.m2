<<<<<<< HEAD
restart
kk = ZZ/101
S = kk[a,b,c,d]
I = monomialCurveIdeal(S,{1,3,4})
betti res I
f = I_1
g = (entries (gens I*random(source gens I, S^{-3})))_0_0
g = I_0

--f,g \in I

h = a --nzd mod f

I' = ideal(f,g):I note: gh\in I'
J' = ideal(f,g*h): I' 

assert(J' == ideal(f)+h*I)

=======
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
>>>>>>> b862f73b3635f9b3f1a9b5fd053de68e6246d84d

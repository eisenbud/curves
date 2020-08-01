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


kk = ZZ/101
R = kk[u,v,w]
m = matrix{
    {0,0,u,0,w},
    {0,u,0,-2*w,0},
    {u,0,w,0,v},
    {0,-2*w,0,v,0},
    {w,0,v,0,0}}
q = det m
sing = ideal diff (vars R,q)
codim sing
degree sing
factor q
singpoint = ideal (u,w)
degree (q+singpoint^6)

d = 4
P = kk[x_0..x_d]
n = map(P^2, P^{d:-1}, (i,j) -> x_(i+j));
I = minors (2,n);
L = apply(binomial(d,2),i->(diff(transpose vars P, diff(vars P, I_i))));
R = kk[z_0..z_(binomial(d,2)-1)];
LR = apply(L, ell -> sub(ell, R));
m = sum apply((binomial(d,2), i-> R_i*LR_i))
q = det m ;
sing = ideal diff (vars R,q);
dim sing
degree sing
pd = primaryDecomposition ideal q
--for the case d=4:
F2 = pd_0_0
F3 = pd_1_0
sing3 = ideal diff (vars R,F3);
codim sing3
--netList primaryDecomposition sing3 -- irreducible+reduced
--degree sing3 == 4
dim sing3
--betti res sing3 -- it's a scroll in P^5
codim (sing3+F2)
degree(sing3+F2)
netList primaryDecomposition (sing3+F2)
dim singularLocus(R/(sing3+F2))
dim (sing3+F2)
radical(sing3+F2)

--scrolls in P5
--type a,b
restart
kk= ZZ/101
a=2;b=3;
d = a+b+1
P = kk[x_0..x_d]

n = map(P^2, P^{d-1:-1}, (i,j) ->if j<=a-1 then x_(i+j) else x_(i+j+1))

I = minors (2,n);
L = apply(binomial(d-1,2),i->(diff(transpose vars P, diff(vars P, I_i))));
R = kk[z_0..z_(binomial(d-1,2)-1)];
LR = apply(L, ell -> sub(ell, R));
m = sum apply((binomial(d-1,2), i-> R_i*LR_i))
q = det m 
sing = trim ideal diff (vars R,q)
--sing == radical sing
dim sing
degree sing
peek'_2 factor q
pd = primaryDecomposition ideal q
netList pd
--for the case d=4:
F2 = pd_0_0
F3 = pd_1_0
sing3 = ideal diff (vars R,F3);
codim sing3
--netList primaryDecomposition sing3 -- irreducible+reduced
--degree sing3 == 4
dim sing3
--betti res sing3 -- it's a scroll in P^5
codim (sing3+F2)
degree(sing3+F2)
netList primaryDecomposition (sing3+F2)
dim singularLocus(R/(sing3+F2))
dim (sing3+F2)
radical(sing3+F2)

--------
--double lines
restart
S = ZZ/101[a,b,c,d]
delta = 4
f = c^delta
g = d^delta
R = S^1/(I = ideal(a^2,a*b, b^2, a*f+b*g))
J = ideal(a^2,b^2):I 
betti (G = res J)
betti (F = res R)
genus (S/J)
genus (S/ideal(a^2,b^2, a*f+b*g))
F.dd
F_4
Ext^3(R,S^{-4})
Ext^4(Ext^3(R,S^{-4}), S^{-4})
Ext^3(S^1/J, S^{-4})

koszul(3, vars S)
koszul(2, vars S)

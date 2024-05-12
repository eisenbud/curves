--the initial ideal of a canonical curve with simple g-2-secant, after Schreyer, Petri:

kk = ZZ/101
inI = g ->(
    S = kk[x_0..x_(g-1)];
    mon1 = ideal flatten for i from 1 to g-3 list for j from i+1 to g-2 list x_i*x_j;
    mon2 = ideal for i from 1 to g-3 list x_(g-1)*x_i^2;
    mon3 = ideal (x_(g-1)*x_(g-2)^3);
    mon1+mon2+mon3)
g = 5
betti res(I =  inI g)
S = ring I
numcols basis (0,Hom(module I, S^1/I)) 
3*g-3+ g^2-1

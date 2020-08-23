restart
k= ZZ/101
ell = (n,d,s)->(
    --ideal of the elliptic curve in P^n, degree d, embedded by a linear series of
    --forms of degree s through 3*s-d points.
S = k[x,y,z];
I = ideal(y^2*z-x*(x-z)*(x+z));
R = S/I;
J1 = (ideal(y,x))^(3*s-d);
J = saturate J1;
f = (gens J)*random(source gens J, R^{n+1:-s});
T = k[a_0..a_n];
I = ker map(R,T,f);
I)

for n from 4 to 10 do <<(n, betti res(I =  ell(n,n+2,4)))<<flush<<endl

betti res ell(6,8,3)
degree I
genus I

i46 : for n from 4 to 10 do <<(n, betti res(I =  ell(n,n+2,4)))<<flush<<endl
           0 1 2 3 4
(4, total: 1 5 9 6 1)
        0: 1 . . . .
        1: . 3 . . .
        2: . 2 9 6 1
           0 1  2  3 4 5
(5, total: 1 7 14 14 7 1)
        0: 1 .  .  . . .
        1: . 7  7  . . .
        2: . .  7 14 7 1
           0  1  2  3  4 5 6
(6, total: 1 12 26 28 20 8 1)
        0: 1  .  .  .  . . .
        1: . 12 24 12  . . .
        2: .  .  2 16 20 8 1
           0  1  2  3  4  5 6 7
(7, total: 1 18 51 63 48 27 9 1)
        0: 1  .  .  .  .  . . .
        1: . 18 51 54 18  . . .
        2: .  .  .  9 30 27 9 1
           0  1  2   3   4  5  6  7 8
(8, total: 1 25 90 142 125 75 35 10 1)
        0: 1  .  .   .   .  .  .  . .
        1: . 25 90 140 100 25  .  . .
        2: .  .  .   2  25 50 35 10 1
           0  1   2   3   4   5   6  7  8 9
(9, total: 1 33 143 286 319 220 110 44 11 1)
        0: 1  .   .   .   .   .   .  .  . .
        1: . 33 143 286 308 165  33  .  . .
        2: .  .   .   .  11  55  77 44 11 1

restart
S = ZZ/32003[H,F,a,b,d,g,u]/ideal(H^2-d, F^2, H*F-u)
K = (-2)*H+(d-2)*F
ev = f -> sub(f, {u=>1, d => g-2})
chi := C -> ev((C+K)*C)
chi H
chi F
chi (a*H+b*F)
C = a*H + (b-a)*F
C = H-K
C = a*H-a*F
ev(C*(C+K))
E = a*(H-d*F)
ev (H*E)
C' = H-K+E
ev (C'*(C'+K))
(chi C')

--in P3:
p = d-> d^2//4 -d +1
p 9
p1 = d -> (d^2-3*d)//6+1
p1 9
netList for i from 8 to 20 list {p i, p1 i}


p' = (d,r) -> (
    m = (d-1)//(r-1);
    eps = d-1 - m*(r-1);
    binomial(m,2)*(r-1)+m*eps
    )
p'(8,3)    
netList for i from 8 to 20 list {p i, p'(i,3)}

netList for d from 1 to 10 list(d, binomial(d-1,2), p'(2*d,5)) 

--r=3
p1' = d -> (
    if d%3 == 0 then 
	(d^2-3*d)//6+1
    else
        (d^2-3*d+2)//6
	)
       
netList for i from 8 to 20 list {p1 i, p1' i}


---
--2m+1 points in P2, no m+2 on a line impose independent conditions on m-ics?
--a "signature" of m+2 on a line in the Burch matrix -- one equn is of deg m+2.

restart
needsPackage "Points"
S = ZZ/32003[a,b,c]

--m+1 points on each of two lines, one point in common:
--still imposes indep cond on m-ics:

for m from 3 to 10 do(
M0 := map(S^1, S^(m+1), matrix{apply(m+1, i->0_S)});
M := map(S^1, S^(m+1), matrix{apply(m+1, i -> i_S)});
M1 := map(S^1, S^(m+1), matrix{apply(m+1, i->1_S)});
line1 = M0||M||M1;
line2 = M||M0||M1;
I = points (line1 | line2);
<< degree I<< 
numcols basis(m, S^1/I) == 2*m+1<<endl
)

----
restart
n=4
kk = ZZ/101
S = kk[x_0..x_(n-1), y_0..y_(n-1)]
Rx = matrix"x_0..x_(n-1)"
Rx = matrix{{x_0..x_(n-1)}}
Ry = matrix{{y_0..y_(n-1)}}
Skx = map(S^n, S^{n:-1}, (i,j) -> if j == (i+1)%n then x_((i+j)%n)
                                  else if j == (i-1)%n then -x_((i+j)%n)
				  else 0)

plane quartic with one node: projection of a genus 2 quintic from P3, projected from a point of the curve.
genus 2 quartic in P3 lies on a quadric in class 2,3

kk = ZZ/101
S = kk[x,y,z]
R0 = S^1/ideal"xy,xz,yz"
R = S^1/ideal"x,y" ++ S^1/ideal"x,z" ++ S^1/ideal"y,z"
mat = transpose matrix {apply(3, i-> 1_S)}

F0 = res R0
F = res R
D = map(F_0,F0_0,mat)

E = extend(F,F0,D)

d = map(R,R0,mat)
ann coker d
ann coker( transpose E_2 | transpose F0.dd_2)
F.dd_1
F0.dd_1


---
--random rational curve ideals
restart
kk = ZZ/32003
T = kk[s,t]
rrci = (r,d) ->(
    S := kk[x_0..x_r];
    phi = map(T,S, random(T^1, T^{(r+1):-d}));
    I = ker phi;
    mingendeg := (min(I_*/degree))_0;
   regI := 1+regularity minimalBetti ker phi;
    regI <= mingendeg+1
    )

rrci(3,5)

netList for r from 3 to 10 list
  for d from 2*r to 2*r+5 list 
     (r,d, rrci(r,d))
(r,n,d) = (6,2,10)
s(r,n,d)
s = (r,n,d) -> binomial(r+n, n) - (n*d+1)
rrci(r,d)

for r from 6 to 10 do(
LL = for d from r+1 to 10 list (for n from 1 to 10 list s(r,n,d));
<<netList LL<<endl
)
r = 7;
d=8;
n = 1
for n from 1 to 10 list s(r,n,d)

p = positions (L = for n from 1 to 10 list s(3,n,7), i -> i>0)
q = p_{0,1}
L_q
s(r,n,d)
s(7,1,8)
binomial(7+1,1)

r = 5
netList for d from 6 to 50 list (for n from 1 to 10 list s(r,n,d))
netList for d from 6 to 50 list rrci(6,d)

----
--canonical curves of genus 6 in PP^5
--Intersection of a quadric with the cone over an elliptic quintic in P4
--E will be plane cubic with a point p. reimbed by conics through p in P4
--add one variable, choose a quadric in P5; intersection should be a canonical curve.

kk = ZZ/101
P2 = kk[a,b,c]
E = ideal(b^2*c-(a-c)*(a+c)*(a-2*c))
conicsp = trim (ideal gens P2 * p)
P4 = kk[x_0..x_4]
E5 = ker map(P2/E, P4, conicsp_*)
betti res E5
P5 = kk[x_0..x_5]
E5cone = sub (E5, P5)
Q = ideal random(P5^1, P5^{-2})
C = trim(E5cone+Q)
betti res C
matrixC = diff(vars P5, transpose gens C)
codim (rk3 = minors(3, matrixC))
degree rk3
radical rk3
--there are 6 rank 3 quadrics. the radical of their ideal is x_0..x_4--the space of the elliptic quintic.

---------
quintic = ideal random(P2^1, P2^{-5})
CPlaneQuintic = ker map(P2/quintic, P5, gens trim (ideal vars P2)^2)
betti res CPlaneQuintic
quadrics = (gens CPlaneQuintic)_{0..5}
matrixC = diff(vars P5, transpose quadrics)
codim (rk3 = minors(3, matrixC))
-- there are no rank 3 quadrics in this case

---trigonal case:
--try the residual of two lines in the int of a cubic with the cone over a rational normal quartic
use P4
RNC4 = minors(2, matrix{{x_0, x_1,x_2,x_3},{
       x_1,x_2,x_3,x_4}})
coneRat = sub(RNC4, P5)
use P5
twolines =gens intersect( ideal(x_0,x_1,x_2,x_3), ideal(x_1, x_2,x_3,x_4))
cubic = ideal(twolines*random(source twolines, P5^{-3}))
Ctrig =  (coneRat+cubic) : (ideal twolines) 
betti res Ctrig
quadrics = (gens Ctrig)_{0..5}
matrixC = diff(vars P5, transpose quadrics)
codim (rk3 = minors(3, matrixC))
degree rk3

---- 
--Flat projection:
restart

S = ZZ/101[x,a..d]
T = ZZ/101[s,t,x]
phi = map (T,S,{x, x*s^3, s^2*t,s*t^2, t^3})
I = ker phi
saturate(I,S_0)
I = intersect{ideal(a,c), ideal "b,a-t"}
J = saturate(I,t)
substitute(J, t => 0)


S = ZZ/101[t,a..d]
I = minors(2, matrix"at, b,ct;b,ct,dt")
J = saturate(I,t)

J0 = trim substitute(J, t=>0)
P = primaryDecomposition J0
J0red = P_0
J0:J0red
degree(J0red/J0)
presentation(J0red/J0)


S = ZZ/101[t,a..d, MonomialOrder => Eliminate 1]

---Trigonal canonical curves of genus 5.
restart
kk = ZZ/32003
S = kk[x_0..x_4]
m = matrix{{x_0,x_1,x_2},{x_1, x_2, x_3}}
Q = flatten entries random(S^1, S^{3:-2})
z = 0_S

h = matrix{{z,z,z,z,z},{Q_0,z,z,z,z},{Q_1,Q_2,z,z,z},
{x_0,x_1,x_2,z,z},{x_1, x_2, x_3,z,z}}
sk = h-transpose h
I = pfaffians(4,sk)
betti res I
rank jacobian I
mm = ideal vars S
(gens I)%(mm^2)

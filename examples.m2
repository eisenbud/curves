--Hilbert scheme of twisted cubic
needsPackage "GenericInitialIdeal"
plane cubic and point:
S = QQ[a,b,d,c]--, MonomialOrder =>Lex ]
I = intersect(ideal"a3+b3+c3, d", ideal(a,b,d))
hilbertPolynomial(S/I, Projective => false)
gens gb I
leadTerm I
lexgin I
gin I
M = matrix"a,b,c;
b,c,d"
J = minors(2, M)
lexgin J
gin J


--- 2 degrees generation conjecture:
--"The ideal of a Brill-Noether general curve,
--is generated in just two degrees.
-- If we assume that a stronger
--form of maximal rank is true, the following program
--tests this numerically in a range of cases.

restart
k=8
r = 3
d = 3*k+3
g = 4*k

x = m -> m*d-g+1
s = m -> binomial(m+r,r)
ide = m -> s m - x m
test = m ->(m, s m, x m, ide m)
rho = (g,r,d) -> g -((r+1)*(g-d+r))
rho(g,r,d)

testGen = (g,r,d) ->(
m := 2;
while s m <= x m do m = m+1;
L := apply(3, i-> ide (m+i));
L1 := {rho(g,r,d), m, ide (m-1)} | apply(2,i -> (r+1)*L_(i)-L_(i+1));
if last L1 < 0 then print(g,r,d)
)

n = 40
candidates = flatten flatten for g from 3 to n list(
    for r from 3 to n list(
	for d from 3 to 3*n list(
	   if rho(g,r,d) >=0 then (g,r,d) else continue)));
#oo
ans = apply(candidates, c -> testGen c);#ans
nulls = select(ans, i -> i === null);#nulls
#ans == #nulls -- true means all these examples would have ideal
ans_0 === null
---
cast = (d) -> floor(d^2/4.0) -d +1
cast1 = d -> floor((d^2-3*d)/6.0) +1
netList for d from 3 to 10 list {d,cast d, cast1 d}

--
kk = ZZ/101
S = kk[x_0..x_3]
T = kk[s,t]
p = random(T^1, T^{4:-5});
I = ker map(T, S, p);
betti res I

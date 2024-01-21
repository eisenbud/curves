newPackage(
          "PlaneCurveLinearSeries",
          Version => "0.1",
          Date => "October 14, 2023",
          Headline => "Linear series on the normalization of a plane curve",
          Authors => {{ Name => "David Eisenbud", 
		  Email => "de@berkeley.edu", 
		  HomePage => "eisenbud.io.github.com"}},
	  PackageExports => {"IntegralClosure"},
          AuxiliaryFiles => false,
          DebuggingMode => true
          )
      export {
	  "canonicalSeries",
	  "geometricGenus",
	  "linearSeries",
	  "projectiveImage",
	  "canonicalImage",
	  "Conductor" -- option
	  }
///
restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
uninstallPackage "PlaneCurveLinearSeries"      
installPackage "PlaneCurveLinearSeries"      
///


geometricGenus = method(Options => {Conductor=>0})
geometricGenus Ring := ZZ => o -> R -> (
    cond := o.Conductor;
    if dim singularLocus R <= 0 then cond = ideal 1_R;
    if cond == 0 then cond = conductor R;
    c := canonicalSeries (R, Conductor => cond);
    if c == 0 then 0 else numcols c)

geometricGenus Ideal := ZZ => o-> I -> geometricGenus((ring I)/I, Conductor => o.Conductor)

linearSeries = method (Options => {Conductor=>null})
linearSeries (Ideal, Ideal) := Matrix =>  o-> (D0, Dinf) ->(
    -- returns a matrix whose elements span the complete linear series |D_0|+base points,
    -- where D_0 \subset R
    -- is the ideal of an effective divisor in the ring R = S of an ACM curve C0,
    -- with normalization C, eg a plane curve
    -- If the conductor ideal cond is known in advance (eg for a nodal curve) then its ideal should be
    -- given with Conductor => cond.
    R := ring D0;
    D0sat := saturate D0;
    Dinfsat := saturate Dinf;

    if dim singularLocus R <= 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else cond = o.Conductor);
    --now cond is the conductor ideal of $R$

    base := saturate(D0sat*cond);
    F := (base)_*_0;--a form of minimal degree that vanishes on D0sat and cond; 
        --Thus F=0 pulls back to the divisor A+D0+cond
	--on the normalization C of C0
    f := degree F;
  A := (ideal F) : base;
  Aminus := saturate(A*Dinfsat);
--    (gens Aminus) * matrix basis(f, Aminus)
    gens image basis(f, Aminus)
)
linearSeries Ideal := o-> D0 -> 
   linearSeries(D0, ideal 1_(ring D0), Conductor => o.Conductor)

canonicalSeries = method(Options => {Conductor=>null})
canonicalSeries Ring := Matrix => o-> R ->(
    --input: homogeneous coordinate ring of a plane curve
    --output: canonical ideal of the desingularization, as an ideal of R
    cond := o.Conductor;
    if dim singularLocus R <= 0 then cond = ideal 1_R;
    if cond === null then cond = conductor R;

    d := degree R;
    if d-3<0 then ideal 0_R else
        gens image basis(d-3, cond)
    )
canonicalSeries Ideal := Matrix => o-> I-> 
       canonicalSeries((ring I)/I, Conductor => o.Conductor)

projectiveImage = method(Options =>{Conductor => null})
projectiveImage(Ideal, Ideal) := Ring => o -> (D0,Dinfty) ->(
--Produce the ideal of the image under the linear series |D0-Dinfty|
    D := linearSeries(D0, Dinfty, Conductor => o.Conductor);
    R := ring D;
    kk := coefficientRing R;
    s := numcols D;
        X := symbol X;
    SS := kk[X_0..X_(s-1)];
    SS/ker map(R, SS, D)
    )

projectiveImage Ideal := Ring => o -> D0 ->
    projectiveImage(D0, ideal(1_(ring D0)), 
	              Conductor => o.Conductor)

projectiveImage Matrix := Ring => o -> M -> (
 -- in this case M is a 1-m matrix respresenting a
 --linear series.
    R := ring M;
    kk := coefficientRing R;
    s := numcols M;
        X := symbol X;
    SS := kk[X_0..X_(s-1)];
    SS/ker map(R, SS, M)
    )

canonicalImage = method(Options => {Conductor => null})
canonicalImage Ring := Ring => o-> R ->(
    --this version takes the homog coord ring
    -- of a plane curve as input, outputs the
    --homogeneous coordinate ring of the canonical image
    projectiveImage canonicalSeries(R, Conductor => o.Conductor)
)

 -* Documentation section *-

beginDocumentation()
doc ///
Key
 PlaneCurveLinearSeries
Headline
 Linear series on the normalization of a plane curve
Description
  Text
   This package implements procedures described in chapters 4 and 14
   of the book "The Practice of Curves", by David Eisenbud and Joe Harris.
  Example
   kk = ZZ/32003
   S = kk[a,b,c]; T = kk[s,t];
   I = ker map(T,S, {s^7, s^3*t^4+s*t^6, t^7});I
   p' = ideal(a,b)
   isSubset(I,p')
   C = S/I
   geometricGenus C
   (primaryDecomposition ideal singularLocus C)/radical
   p = sub(p', C)
  Text
   We see that p is a smooth point of C, which is a singular 
   rational curve; in fact  singularity at s=0 is the simplest
   singularity with two characteristic pairs. 
   It has arithmetic genus 15, but since it is
   the image of P^1 it is rational:
  Example
   geometricGenus C
   L = for i from 0 to 6 list (rank source linearSeries (p^i)) 
SeeAlso
 geometricGenus

///

doc ///
Key
 canonicalSeries
 (canonicalSeries, Ring)
 (canonicalSeries, Ideal)
 [canonicalSeries, Conductor]
Headline
 Canonical series of the normalization of a plane curve
Usage
 M = canonicalSeries R
Inputs
 R: Ring
  ring of a plane curve
Outputs
 M: Matrix
  a 1 x g matrix representing the canonical series
Description
  Text
   Computing the canonical linear series
  Example
   kk = QQ
   S = kk[x,y,z]
   C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
   C2 = ideal(x^2+y^2+z^2) --nonsingular conic
   C3 = ideal (x^4+y^4+z^4) -- smooth curve of genus 3
   canonicalSeries(S/C1)
   canonicalSeries(S/C2)
   canonicalSeries(S/C3)
///
doc ///
Key
 geometricGenus
 (geometricGenus, Ring)
 (geometricGenus, Ideal)
 [geometricGenus, Conductor]
Headline
 Geometric genus of a (singular) plane curve
Usage
 g = geometricGenus R
 g = geometricGenus I
Inputs
 R: Ring
  homogeneous coordinate ring of a plane curve
 I: Ideal
  defining a plane curve
 Conductor: Ideal
  the conductor of R (if not given, it's computed)
Outputs
 g:ZZ
Description
 Text
   The geometric genus of a plane curve C0 is the genus of the normalization of C0
 Example
   kk = QQ
   S = kk[x,y,z]
   C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
   C2 = ideal(x^2+y^2+z^2)
   C3 = ideal (x^4+y^4+z^4)
   geometricGenus C1
   geometricGenus C2
   geometricGenus C3
 Text
   Every hyperelliptic curve of genus
   g can be represented as a plane curve of degree
   g+2 with a g-fold ordinary singularity, and thus
   conductor equal to the (g-1)st power of the maximal
   ideal. As of 1/20/2024, Macaulay2 crashes on computing
   the conductor when g >= 6, but knowing the 
   conductor one can go much farther:
  
   We make a general hyperelliptic curve of genus
   g with singularity at q'.

  Example
   g = 20
   S = ZZ/101[a,b,c]
   q' = ideal(a,b);
  Text
  Example
   I = q'^g
   C = S/(ideal random(g+2, I));
   p = sub(p', C);
   q = sub(q', C);
   geometricGenus (C, Conductor => q'^(g-1))

SeeAlso
 canonicalSeries
      ///

doc ///
Key 
 linearSeries
 (linearSeries, Ideal)
 (linearSeries, Ideal, Ideal)
 [linearSeries, Conductor]
Headline
 compute a linear series
Usage
 D = linearSeries Dplus
 D = linearSeries (Dplus, Dminus)
Inputs
 Dplus: Ideal
   in the homogeneous coordinate ring A of a plane curve C
 Dminus: Ideal   
   in A
Outputs
 D: Matrix
   of size 1 x dim H^0(Dplus-Dminus). Entries are a basis of |Dplus - Dminus|
Description
  Text
   A quintic plane curve with an ordinary triple point
   and two more marked points:
  Example
   S = ZZ/32003[a,b,c]
   p = ideal(a,b)
   p1' = ideal(b,c)
   p2' = ideal(a,c)
   marked = intersect (p^3, p1', p2')
   C = S/(random(5, marked))
   red = map(C,S)
   p1 = red p1' 
   p2 = red p2'
  Text
   Since the delta invariant of a triple point is 3, the
   geometric genus of C is 3 less than the arithmetic genus computed natively,
   and the conductor is the square of the maximal ideal:
  Example
   genus C
   g = geometricGenus C
   conductor C
   m = 10
   e=2
   netList{
       {"degree: "} | apply(m, i->(i+3-e)),
       {"chi: "} | apply(m, i->(i+3-e -g+1)),
       {"computed: "} | apply(m, i-> numgens trim ideal linearSeries(p2^(i+3), p1^e))
   }
References
 "The Practic of Algebraic Curves" by David Eisenbud and Joe Harris
Caveat
 A bit slower in characteristic 0
SeeAlso
 conductor
 geometricGenus
///

doc///
Key
 projectiveImage
 (projectiveImage, Ideal)
 (projectiveImage, Matrix) 
 (projectiveImage, Ideal, Ideal)
 [projectiveImage, Conductor]
Headline
 Projective image of the map defined by a divisor or matrix
Usage
 I = projectiveImage Dplus
 I = projectiveImage (Dplus, Dminus)
Inputs
 Dplus: Ideal
   in the homogeneous coordinate ring A of a plane curve C
 Dminus: Ideal   
   in A
Outputs
 I: Ideal
   the ideal of the image curve
Description
  Text
   The output ideal is the ideal of polynomial relations
   among the generators of the linear series |Dplus-Dminus|.
   
   If the curve C = ring Dplus is a nonsingular plane cubic,
   then every embedding of C is arithmetically Gorenstein,
   as the following example suggests:
  Example
   S = ZZ/101[a,b,c]
   p' = ideal(a-b, c)
   C = S/ideal"a3-b3+c3"
   p = sub (p', C)
   netList for d from 3 to 7 list
       betti res ideal projectiveImage p^d
SeeAlso
 geometricGenus
 canonicalImage
///

doc///
Key
 canonicalImage
 (canonicalImage, Ring)
 [canonicalImage, Conductor]
Headline
 canonical model of the normalization of a plane curve
Usage
 R' = canonicalImage R
Inputs
 R: Ring
   the homogeneous coordinate ring of a plane curve
Outputs
 R': Ring
   the homogeneous coordinate ring of the canonical image of the normalization
Description
  Text
   The output is 
   the homogeneous coordinate ring 
   of the canonical image of the normalization
   the given curve.
   
   For example,  a plane
   sextic with 4 nodes is a curve of genus 10-4 = 6,
   so its canonical image is a curve of degree 10 in P5

  Example
   P5 = ZZ/101[x_0..x_5]
   P2 = ZZ/101[a,b,c]
   fourpoints = {
       ideal(a,b), 
       ideal(b,c), 
       ideal(a,c), 
       ideal(a-b, a-c)
       }
   nodes = intersect apply(fourpoints, p -> p)
   sings' = intersect apply(fourpoints, p -> p^2)
   C0 = P2/(ideal random(6, sings'))
   sings = sub (sings', C0)
   conductor C0 == sub(nodes, C0)
   C = canonicalImage C0
   betti res ideal C
   delPezzo = P5/ker(map(P2, P5, gens image basis (3,intersect nodes)))
   betti res ideal delPezzo
   
SeeAlso
 geometricGenus
 canonicalImage
///

doc///
Key
 Conductor
Headline
 Option to avoid computation
Usage
 M = geometricGenus(C,Conductor => cond)
Inputs
 C: Ring
 cond: Ideal
  the conductor of C

Description
  Text
   Computing the conductor involves computing the
   normalization, which is potentially expensive.
   If it is known in advance (as in the case of an
   ordinary multiple point) the user can insert it
   to avoid the computation.
   
SeeAlso
 geometricGenus
///


-* Test section *-

TEST///
S = ZZ/32003[a,b,c]
I = ideal"a3+b3-c3"
p'= ideal(a,b-c)
isSubset(I,p')
R = S/I
p = sub(p',R)
assert (geometricGenus R == 1)
assert(canonicalSeries R == matrix{{1_R}})
L = for d from 3 to 7 list rank source ((res ideal projectiveImage p^d).dd_(d-2))
assert(all(L, ell->ell == 1))
///

TEST///
restart
loadPackage("PlaneCurveLinearSeries", Reload => true)
S = QQ[x,y,z]
sing3 = (ideal(x,y))^3
sing1 = (ideal(x,z))^2
C4 = ideal random(5, sing3) -- quintic with ord 3-point; genus 3, hyperell.
C5 = ideal random(5, sing1) -- quintic with node, genus 5
C6 = ideal random(5, intersect(sing1, sing3))-- quintic with ord 3-point and a node; genus 2
assert (numgens canonicalSeries C4 == 3)
assert (numgens canonicalSeries C5 == 5)
assert (numgens canonicalSeries C6 == 2)
assert (geometricGenus C6 == 2)
///
 
TEST///
--two characteristic pairs
restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
kk = ZZ/32003
S = kk[a,b,c]; T = kk[s,t];
I = ker map(T,S, {s^7, s^6*t, s^3*t^4+s*t^6+t^7});I
R = S/I
assert (geometricGenus R == 0)
use S
p' = ideal(a-c,b+c)
isSubset(I,p')
radical ideal singularLocus R
--p' is a smooth point of the curve.
p = sub(p', R)
L = for i from 0 to 6 list (rank source linearSeries (p^i)) 
assert(L == {1, 2, 3, 4, 5, 6, 7})
assert(degree projectiveImage p^3 == 3)
///

TEST///
 -* canonicalIdeal, geometricGenus *-
restart
load "planeCurves.m2"
kk = QQ
S = kk[x,y,z]
C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
C2 = ideal(x^2+y^2+z^2)
C3 = ideal (x^4+y^4+z^4)
sing = (ideal(x,y))^3
C4 = ideal random(5, sing) -- quintic with ord 3-point; genus 3, hyperell.
C5 = ideal random(5, sing+(ideal(x,z))^2) -- quintic with ord 3-point and a node; genus 2
canonicalSeries(S/C1)
canonicalSeries(S/C2)
canonicalSeries(S/C3)
canonicalSeries(C4)
canonicalSeries(C5)

canonicalSeries C1 == 0
canonicalSeries C2 == 0
canonicalSeries C3 == ideal vars ((ring C3)/C3)

geometricGenus C1 == 0
geometricGenus C2 == 0
geometricGenus C3 == 3
geometricGenus C4 == 3
///


end--

///
restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
uninstallPackage "PlaneCurveLinearSeries"      
installPackage "PlaneCurveLinearSeries"      
check "PlaneCurveLinearSeries"      
viewHelp PlaneCurveLinearSeries
///

Here are many small examples; some should be in the docs, some
in the TESTs, some deleted.

restart
load "PlaneCurveLinearSeries.m2"
kk = ZZ/101
S = kk[x,y,z]
use S
C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
C2 = ideal(x^2+y^2+z^2)

sing = (ideal (x,y))^2 -- doublePoint
sing = (ideal (x,y))^3 -- triplePoint
use S
C3 = ideal random(6, sing) -- quintic with ord 3-point; genus 3, hyperell.
use S
R = S/C3
geometricGenus C3
geometricGenus R
omega = canonicalSeries R
numgens omega
(linearSeries ideal z) -- does not return Cartier divisors
sections ideal z -- right aswer
projectiveImage ideal (x^3)
degree singularLocus projectiveImage ideal (z^2)
genus oo

geometricGenus oo

projectiveImage oo
ideal z
(linearSeries ideal z^2)
gens trim ideal sections(ideal z^2, ideal 1_R)
ideal R
conductor R

projectiveImage (ideal z^2, ideal 1_R)
minimalBetti oo

D0 = ideal (z^4)
Dinfty = ideal (x+y+z)
Ds = linearSeries(D0,Dinfty);#Ds
I = projectiveImage(D0, Dinfty)
I = projectiveImage (ideal (z^2), ideal 1_R);
numgens
minimalBetti I


--quintic with 3 double points
restart
load "PlaneCurveLinearSeries"
S = ZZ/32003[a,b,c]
p1 = ideal(a,b)
p2 = ideal(b,c)
p3 = ideal(a,c)
p4S = ideal (a-b, a-c)
sings = intersect (p1^2, p2^2, p3^2, p4S); 

I = ideal random(5, sings)--quintic with 3 double points
R = S/I
red = map(R,S)

genus R == 6 -- arithmetic genus
geometricGenus R == 3 -- curve smooth away from the 3 double points
degree singularLocus R == 3 -- another confirmation
conductor R == ideal (b*c, a*c, a*b) -- and yet another
omega = canonicalSeries R;
numgens omega

p4 = red p4S
for i from 1 to 11 list rank source linearSeries p4^i


--smooth plane cubic

restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
--Plane cubic with one node:
S = ZZ/32003[a,b,c]
p1 = ideal(a,c)
p2S = ideal (b, c)
sings = intersect (p1^2, p2S)
I = ideal random(3, sings)--rational plane cubic with a node
I = ideal (c^3-a^2*b) -- rational plane cubic with a cusp
R = S/I
conductor R
red = map(R,S)
geometricGenus R
p2 = red p2S
linearSeries (D0=p2) 
for i from 0 to 10 list rank source linearSeries p2^i



--S = QQ[a,b,c] -- using QQ is substantially slower
S = ZZ/32003[a,b,c]
p1 = ideal(a,b)
p2 = ideal(b,c)
p3 = ideal(a,c)
p4S = ideal (a-b, a-c)
sings = intersect (p1^2, p2^2, p3^2, p4S); 

I = ideal random(5, sings)--quintic with 3 double points
R = S/I
red = map(R,S)

genus R == 6 -- arithmetic genus
geometricGenus R == 3 -- curve smooth away from the 3 double points
degree singularLocus R == 3 -- another confirmation
conductor R == ideal (b*c, a*c, a*b) -- and yet another
omega = canonicalSeries R;
numgens omega

p4 = red p4S
for i from 1 to 11 list rank source linearSeries p4^i

--further examples
restart
loadPackage("PlaneCurveLinearSeries", Reload => true)
S = ZZ/32003[a,b,c]
p = ideal(a,b)
p1' = ideal(b,c)
p2' = ideal(a,c)

use S
marked = intersect (p^3, p1', p2')
degree marked
C = S/(random(5, marked))
genus C
g = geometricGenus C
conductor C
red = map(C,S)
p1 = red p1'
p2 = red p2'

--with a curve of degree 4 and a double point (g=2), the linear series 3p_2-p1 seems to be
--special, 4p_2-p_1 nonspecial (as it must be) but 5p_2-p1 has an extra section, dim 4
m = 10
e=2
netList{
    {"degree: "} | apply(m, i->(i+3-e)),
    {"chi: "} | apply(m, i->(i+3-e -g+1)),
    {"computed: "} | apply(m, i-> numgens trim ideal linearSeries(p2^(i+3), p1^e))
}

--with a curve of degree 5, and a double point,
degree 7 seems to be nonspecial (dim = 7-5+1, but degree 8 jumps by 2.




restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
--Plane cubic with one node:
S = ZZ/32003[a,b,c]
p1 = ideal(a,c)
p2S = ideal (b, c)
sings = intersect (p1^2, p2S)
I = ideal random(3, sings)--rational plane cubic with a node
I = ideal (c^3-a^2*b) -- rational plane cubic with a cusp
R = S/I
conductor R
red = map(R,S)
geometricGenus R
p2 = red p2S
linearSeries (D0=p2) 
for i from 0 to 10 list rank source linearSeries p2^i


test = method(Options => {Conductor=>null})
test ZZ := ZZ => o -> n -> (
    out := o.Conductor;
    print out;
    if out === null then(
	print "here";  out = n);
    out)

3 == test 3
7 == test(3, Conductor => 7)

restart
geometricGenus = method(Options => {Conductor=>0})
geometricGenus Ideal := ZZ => o -> I -> (
    R := (ring I)/I;
    cond := o.Conductor;
--    if dim singularLocus R <= 0 then cond = ideal 1_R;
    print cond;
    if cond == 0 then (
	print "here"; cond = conductor R);
    cond)
  


g=4
S = ZZ/101[a,b,c]
q' = ideal(a,b)
C = S/random(g+2, q'^g)
q = sub(q', C)
geometricGenus (C, Conductor => q^(g-1))

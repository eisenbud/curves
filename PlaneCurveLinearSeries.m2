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
	  "Conductor", -- option
	  "canonicalIdeal",
	  "geometricGenus",
	  "sections", 
	  "linearSeries",
	  "projectiveImage",
	  "canonicalImage"}
      
canonicalIdeal = method(Options => {Conductor=>null})
canonicalIdeal Ring := Ideal => o-> R ->(
    --input: homogeneous coordinate ring of a plane curve
    --output: canonical ideal of the desingularization, as an ideal of R
    cond := o.Conductor;
    if dim singularLocus R <= 0 then cond = ideal 1_R;
    if cond === null then cond = conductor R;

    d := degree R;
    if d-3<0 then ideal 0_R else
        ideal image basis(d-3, cond)
    )
canonicalIdeal Ideal := Ideal => o-> I ->(
    --this version takes the ideal of a plane curve as input
    S := ring I;
    R := S/I;
    canonicalIdeal(R, o)
)

geometricGenus = method(Options => {Conductor=>null})
geometricGenus Ideal := ZZ => o-> I -> (
-*    R := (ring I)/I;
    cond := o.Conductor;
    if dim singularLocus R <= 0 then cond = ideal 1_R;
    if cond === null then cond = conductor R;
*-
    c := canonicalIdeal (I, Conductor => o.Conductor);
    if c == 0 then 0 else numgens c)
geometricGenus Ring := ZZ => o-> R -> geometricGenus ideal R


linearSeries = method (Options => {Conductor=>null})
linearSeries (Ideal, Ideal) :=  o-> (D0, Dinf) ->(
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

--cond := conductor R;

    
--    base := intersect(D0sat,cond);
    base := saturate(D0sat*cond);
    F := (base)_*_0;--a form of minimal degree that vanishes on D0sat and cond; 
        --Thus F=0 pulls back to the divisor A+D0+preimage(conductor)
	--on the normalization C of C0
--pF := primaryDecomposition ideal F;
--netList pF
    f := degree F;
--    A := ((ideal F : D0): cond);
--error();
  A := (ideal F) : base;
--  Aminus := intersect(A, Dinfsat);
  Aminus := saturate(A*Dinfsat);
--  error(); 
--  pFr := (primaryDecomposition ideal F) /radical;
    (gens Aminus) * matrix basis(f, Aminus)
)
linearSeries Ideal := o-> D0 -> linearSeries(D0, ring D0)

///
--two characteristic pairs

restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
kk = ZZ/32003
S = kk[a,b,c]; T = kk[s,t];
I = ker map(T,S, {s^7, s^6*t, s^3*t^4+s*t^6+t^7});I
R = S/I
genus R
geometricGenus R
use S
p = ideal(a-c,b+c)
radical ideal singularLocus R
isSubset(I,p)
--p is a smooth point of the curve.
p = sub(p,R)
for i from 0 to 6 list rank source linearSeries (p^i)

radical ideal singularLocus R

assert (geometricGenus R == 0)
red = map(R,S)
use S
p = ideal(b,c)
for i from 0 to 6 list rank source linearSeries red(p^i)

///

///
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



--S = QQ[a,b,c] -- substantially slower
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
omega = canonicalIdeal R;
numgens omega

p4 = red p4S
for i from 1 to 11 list rank source linearSeries p4^i
///

///
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
e=1
netList{
    apply(m, i-> numgens trim ideal linearSeries(p2^(i+3))),
    apply(m, i-> numgens trim ideal linearSeries(p2^(i+3), p1^e)),
    apply(m, i->(i+3-e -g+1)),
    apply(m, i->(i+3-e))}
--with a curve of degree 5, and a double point,
degree 7 seems to be nonspecial (dim = 7-5+1, but degree 8 jumps by 2.
///


///
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

-------------------------------------
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
omega = canonicalIdeal R;
numgens omega

p4 = red p4S
for i from 1 to 11 list rank source linearSeries p4^i
///



projectiveImage = method(Options =>{Conductor => null})
projectiveImage(Ideal, Ideal) := Ideal => o -> (D0,Dinfty) ->(
--Produce the ideal of the image under the linear series |D0-Dinfty|
    R := ring D0;
    if dim singularLocus R <= 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else cond = o.Conductor);

    D0plus := intersect(D0,cond);
    m := min flatten degrees D0plus;
    G := ideal random(m, D0plus);
    A := G:D0plus;
    baseLocus := intersect(A, Dinfty, cond);
--    sections := gens trim truncate(m, baseLocus);
    sections := gens image basis(m,baseLocus);

    s := numcols sections;
    kk := coefficientRing R;
    X := symbol X;
    SS := kk[X_0..X_(s-1)];
    
    ker map(R, SS, sections)
    )

projectiveImage Ideal := Ideal => o -> D0 ->(
    projectiveImage(D0, ideal(1_(ring D0)))
    )

TEST///
restart
loadPackage("PlaneCurveLinearSeries", Reload => true)
S = QQ[x,y,z]
sing3 = (ideal(x,y))^3
sing1 = (ideal(x,z))^2
C4 = ideal random(5, sing3) -- quintic with ord 3-point; genus 3, hyperell.
C5 = ideal random(5, sing1) -- quintic with node, genus 5
C6 = ideal random(5, intersect(sing1, sing3))-- quintic with ord 3-point and a node; genus 2
assert (numgens canonicalIdeal C4 == 3)
assert (numgens canonicalIdeal C5 == 5)
assert (numgens canonicalIdeal C6 == 2)
assert (geometricGenus C6 == 2)
///

 -* Documentation section *-
///
restart
loadPackage"PlaneCurveLinearSeries"
///
      beginDocumentation()

      doc ///
      Key
       PlaneCurveLinearSeries
      Headline
       Linear series on the normalization of a plane curve 
      Description
        Text
	 Computing the canonical ideal
        Example
         kk = QQ
         S = kk[x,y,z]
         C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
         C2 = ideal(x^2+y^2+z^2) --nonsingular conic
         C3 = ideal (x^4+y^4+z^4) -- smooth curve of genus 3

         canonicalIdeal(S/C1)
         canonicalIdeal(S/C2)
         canonicalIdeal(S/C3)
	 
      References
      Caveat
      SeeAlso
      Subnodes
      ///

      doc ///
      Key
       geometricGenus
      Headline
       Geometric genus of a (singular) plane curve
      Usage
       (geometricGenus, Ring)
       (geometricGenus, Ideal)
       [geometricGenus, Conductor]
      Inputs
      Outputs
      Consequences
        Item
      Description
        Text
        Example
         kk = QQ
         S = kk[x,y,z]
         C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
         C2 = ideal(x^2+y^2+z^2)
         C3 = ideal (x^4+y^4+z^4)
	 
	 geometricGenus C1
 	 geometricGenus C2
 	 geometricGenus C3
      Contributors
      References
      Caveat
      SeeAlso
      ///

      -* Test section *-


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
canonicalIdeal(S/C1)
canonicalIdeal(S/C2)
canonicalIdeal(S/C3)
canonicalIdeal(C4)
canonicalIdeal(C5)

canonicalIdeal C1 == 0
canonicalIdeal C2 == 0
canonicalIdeal C3 == ideal vars ((ring C3)/C3)

geometricGenus C1 == 0
geometricGenus C2 == 0
geometricGenus C3 == 3
geometricGenus C4 == 3
///
    
TEST///
 -* linearSeries *-
///

end--
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
omega = canonicalIdeal R
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


---jetsam
-*
linearSeries Ideal :=  o-> D0 ->(
    -- Note: bad news if D0 is an ideal of S rather than R = S/I.
    -- returns a matrix whose elements span the complete linear series |D_0|+base points,
    -- where D_0 \subset R
    -- is the ideal of an effective divisor in the ring R = S of an ACM curve C0,
    -- with normalization C, eg a plane curve
    -- If the conductor ideal cond is known in advance (eg for a nodal curve) then its ideal should be
    -- given with Conductor => cond.
    R := ring D0;
    D0sat := saturate D0;

    if dim singularLocus R <= 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else cond = o.Conductor);
    --now cond is the conductor ideal of $R$

--    base := intersect(D0sat,cond);
    base := saturate(D0sat*cond);    
    F := (base)_*_0;--a form of minimal degree that vanishes on D0sat and cond; 
        --Thus F=0 pulls back to the divisor A+D0+preimage(conductor)
	--on the normalization C of C0
    f := degree F;
    A := (ideal F : base);
--    Aplus := intersect(A, cond);
    Aplus := saturate(A * cond);    
    gens Aplus * matrix basis(f, Aplus)
    )
*-

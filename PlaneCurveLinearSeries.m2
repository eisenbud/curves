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
	  "projectiveImage"}
      
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

///
restart
loadPackage("PlaneCurveLinearSeries", Reload => true)
S = QQ[x,y,z]
sing3 = (ideal(x,y))^3
sing1 = (ideal(x,z))^2
C4 = ideal random(5, sing3) -- quintic with ord 3-point; genus 3, hyperell.
C5 = ideal random(5, sing1) -- quintic with ord 3-point and a node; genus 2
C6 = ideal random(5, intersect(sing1, sing3))
canonicalIdeal C4
canonicalIdeal C5
canonicalIdeal C6
geometricGenus C6
///

linearSeries = method (Options => {Conductor=>null})
linearSeries Ideal :=  o-> D0 ->(
    -- returns a matrix whose elements span the complete linear series |D_0|+base points,
    -- where D_0 \subset R
    -- is the ideal of an effective divisor in the ring R = S of an ACM curve C0,
    -- with normalization C, eg a plane curve
    -- If the conductor ideal cond is known in advance (eg for a nodal curve) then its ideal should be
    -- given with Conductor => cond.
    R := ring D0; -- ring ring of C0
    if dim singularLocus R <= 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else cond = o.Conductor);
    --now cond is the conductor ideal.
    
    F := (intersect(D0,cond))_*_0;--a form of minimal degree that vanishes on D0 and cond; 
    --Thus F=0 pulls back to the divisor A+D0+cond on the normalization C of C0
    f := degree F;
    Aplus := (ideal F : D0); -- pullsback to the ideal of the divisor A+cond on C
    D := gens intersect((ideal basis(degree F, R)), Aplus); -- a matrix
    --whose entries are a basis of the forms of the same degree as F and vanish on Aplus.
    D
    )

linearSeries (Ideal, Ideal) :=  o-> (D0, Dinf) ->(
    -- returns a matrix whose elements span the complete linear series |D_0|+base points,
    -- where D_0 \subset R
    -- is the ideal of an effective divisor in the ring R = S of an ACM curve C0,
    -- with normalization C, eg a plane curve
    -- If the conductor ideal cond is known in advance (eg for a nodal curve) then its ideal should be
    -- given with Conductor => cond.
    R := ring D0; -- ring ring of C0
    if dim singularLocus R <= 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else cond = o.Conductor);
    --now cond is the conductor ideal.
    
    F := (intersect(D0,cond))_*_0;--a form of minimal degree that vanishes on D0 and cond; 
    --Thus F=0 pulls back to the divisor A+D0+cond on the normalization C of C0
    f := degree F;
    Aplus := (ideal F : D0); -- pullsback to the ideal of the divisor A+cond on C
    D := gens intersect((ideal basis(degree F, R)), Aplus, Dinf); -- a matrix
    --whose entries are a basis of the forms of the same degree as F and vanish on Aplus and Dinf
    D
    )



///
restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
S = QQ[a,b,c]
fermat = d -> ideal sum(#gens S, i-> (-1)^i*S_i^d)
fermat 3
R = S/fermat 3
p = ideal(a-b,c)
degree p
D0 = p^5
Dinf = p
degree D0
(D, Aplus, cond) = linearSeries D0
Dlist = flatten entries D
apply(Dlist/(g -> ideal g), I -> isSubset(I, Aplus))
degree ideal D == degree Aplus
P = QQ[x_0..x_(numcols D -1)]
ker map(R,P,D)
betti res oo
///
linearSeries (Ideal, Ideal) := Ideal => o-> (D0,Dinfty) ->(
    R := ring D0;
    if dim singularLocus R <= 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else 
    cond = o.Conductor);

    D0plus := intersect(D0,cond);
    m := min flatten degrees D0plus;
    G := ideal random(m, D0plus);
    A := G:D0plus;
    Hs := trim ideal image basis (m, intersect{A,Dinfty, cond});
 apply (Hs_*, H -> (ideal H):(intersect(A,Dinfty)))
    )

    
sections = method(Options =>{Conductor => null})
sections(Ideal, Ideal) := Ideal => o -> (D0,Dinfty) ->(
--Produce the ideal of the image under the linear series |D0-Dinfty|
    R := ring D0;
    if dim singularLocus R <= 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else 
    cond = o.Conductor);

    D0plus := intersect(D0,cond);
    m := min flatten degrees D0plus;
    G := ideal random(m, D0plus);
    A := G:D0plus;
    baseLocus := intersect(A, Dinfty, cond);
--  gens trim truncate(m, baseLocus);
    gens image basis(m,baseLocus)
)

sections Ideal := Matrix => o-> D0 ->(
    sections(D0, ideal(1_(ring D0)))
    )

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

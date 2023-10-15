--Given C_0 \subset \PP^2, compute the canonical series on the normalization and determine linear equivalence.
--
newPackage(
          "PlaneCurveLinearSeries",
          Version => "0.1",
          Date => "October 14, 2023",
          Headline => "Linear series on the normalization of a plane curve",
          Authors => {{ Name => "David Eisenbud", 
		  Email => "de@berkeley.edu", 
		  HomePage => "eisenbud.io.github.com"}},
	  PackageExports => {"IntegralClosure", "Truncations"},
          AuxiliaryFiles => false,
          DebuggingMode => true
          )

      export {
	  "Conductor", -- option
	  "TargetRing", -- option
	  "VariableName", --option
	  "canonicalIdeal",
	  "geometricGenus",
	  "linearSeries",
	  "projectiveImage"}
      
canonicalIdeal = method(Options => {Conductor=>null})
canonicalIdeal Ring := Ideal => o-> R ->(
    --input: homogeneous coordinate ring of a plane curve
    --output: canonical ideal of the desingularization, as an ideal of R
    if dim singularLocus R == 0 then cond := ideal 1_R else(
          if o.Conductor === null then cond = conductor R else 
	  cond = o.Conductor);
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
    R := ring I;
        if dim singularLocus R == 0 then cond := ideal 1_R else(
          if o.Conductor === null then cond = conductor R else 
	  cond = o.Conductor);
    c := canonicalIdeal (I, Conductor => cond);
    if c == 0 then 0 else numgens canonicalIdeal R)

geometricGenus Ring := ZZ => o-> R -> geometricGenus ideal R

linearSeries = method (Options => {Conductor=>null})
linearSeries (Ideal, Ideal) := Ideal => o-> (D0,Dinfty) ->(
    R := ring D0;
    if dim singularLocus R == 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else 
    cond = o.Conductor);
    D0plus := intersect(D0,cond);
    m := min flatten degrees D0plus;
    G := ideal random(m, D0plus);
    A := G:D0plus;
    Dinftyplus := intersect(Dinfty, cond);
    Hs := trim ideal image basis (m, intersect(A,Dinftyplus));
    apply (Hs_*, H -> (ideal H):(intersect(A,Dinfty)))
    )

projectiveImage = method(
    Options =>{Conductor => null, TargetRing => null, VariableName => "X"})
projectiveImage(Ideal, Ideal) := Ideal => o -> (D0,Dinfty) ->(
--Produce the ideal of the image under the linear series |D0-Dinfty|
    R := ring D0;
    if dim singularLocus R == 0 then cond := ideal 1_R else(
    if o.Conductor === null then cond = conductor R else 
    cond = o.Conductor);
    D0plus := intersect(D0,cond);
    m := min flatten degrees D0plus;
    G := ideal random(m, D0plus);
    A := G:D0plus;
    baseLocus := intersect(A, Dinfty, cond);
    sections := gens trim truncate(m, baseLocus);
--    sections := gens image basis(m,baseLocus);
    if o.TargetRing =!=null then SS := TargetRing else(

    s := numcols sections;
    kk := coefficientRing R;
    X := o.VariableName;
    SS = kk[X_0..X_(s-1)]);
    
    ker map(R, SS, sections)
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
        Example
         kk = QQ
         S = kk[x,y,z]
         C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
         C2 = ideal(x^2+y^2+z^2)
         C3 = ideal (x^4+y^4+z^4)

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

canonicalIdeal(S/C1)
canonicalIdeal(S/C2)
canonicalIdeal(S/C3)

canonicalIdeal C1 == 0
canonicalIdeal C2 == 0
canonicalIdeal C3 == ideal vars ((ring C3)/C3)

geometricGenus C1 == 0
geometricGenus C2 == 0
geometricGenus C3 == 3
///
    
TEST///
 -* linearSeries *-
///

end--
restart
load "planeCurves.m2"
kk = QQ
S = kk[x,y,z]
sing = (ideal vars S)^2 -- triplepoint
C3 = rand (5, sing) -- quintic with ord 3-point; genus 3, hyperell.
C1 = ideal (y^3 - x^2*(x-z)) -- cubic with a node; geometric genus 0
C2 = ideal(x^2+y^2+z^2)
sing = (ideal (x,y))^2 -- doublePoint
sing = (ideal (x,y))^3 -- triplePoint
C3 = random(5, sing) -- quintic with ord 3-point; genus 3, hyperell.
use S
R = S/C1
R = S/C2
R = S/C3
geometricGenus R
conductor R

D0 = ideal (z^4)
Dinfty = ideal (x+y+z)
Ds = linearSeries(D0,Dinfty);#Ds
I = projectiveImage(D0, Dinfty)
betti res I

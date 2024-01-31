newPackage(
          "PlaneCurveLinearSeries",
          Version => "0.1",
          Date => "October 14, 2023",
          Headline => "Linear series on the normalization of a plane curve",
          Authors => {{ Name => "David Eisenbud", 
		  Email => "de@berkeley.edu", 
		  HomePage => "eisenbud.io.github.com"}},
	  PackageExports => {"IntegralClosure","PrimaryDecomposition","ReesAlgebra"},
          AuxiliaryFiles => false,
          DebuggingMode => true
          )
      export {
	  "canonicalSeries",
	  "geometricGenus",
	  "linearSeries",
	  "projectiveImage",
	  "canonicalImage",
	  "fromCoordinates",
	  "toCoordinates",
	  "addition",
	  "Conductor", -- option for linearSeries etc
	  "ConductorReduction", -- option for linearSeries
	  "Check", -- option for localMinimalReduction
	  "ShowBase"-- option for linearSeries
	  }
      
	   
--	  "Tries"
--	  }
///
restart
loadPackage ("PlaneCurveLinearSeries", Reload => true)
uninstallPackage "PlaneCurveLinearSeries"      
installPackage "PlaneCurveLinearSeries"      
check"PlaneCurveLinearSeries"      
///
toCoordinates = method()
toCoordinates Ideal := List => I -> (
    --I should be a complete intersection of linear
    --forms, defining a point.
    R := ring I;
    D := diff(transpose gens I, vars R);
    (entries transpose syz D)_0)

fromCoordinates = method()
   --construct ideal of point on a curve in P3 from its coordinates
fromCoordinates (List, Ring) := Ideal =>  (P, C) ->(
    PC := sub (matrix {toList P}, C);
    I := ideal(vars C * (syz PC));
    if dim I == 0 then error"point does not lie on curve";
    I)
fromCoordinates (ZZ,ZZ,ZZ, Ring) := Ideal => (x,y,z, R) -> 
    fromCoordinates (toList(x,y,z),R)

geometricGenus = method(Options => {Conductor=>0})
geometricGenus Ring := ZZ => o -> R -> (
    cond := o.Conductor;
    if dim singularLocus R <= 0 then cond = ideal 1_R;
    if cond == 0 then cond = conductor R;
    c := canonicalSeries (R, Conductor => cond);
    if c == 0 then 0 else numcols c)

geometricGenus Ideal := ZZ => o-> I -> geometricGenus((ring I)/I, Conductor => o.Conductor)

///
restart
debug loadPackage"PlaneCurveLinearSeries"
S = ZZ/2[a,b,c]
pS = ideal(a,b)
sing = pS^5
R = S/random(6, sing)
p = sub(pS, R)
isLocalMinimalReduction(ideal random(5, p^5), p^5, 10)
localMinimalReduction (p^3)
localMinimalReduction (p^3, Check => true)
canonicalSeries R
///

isLocalMinimalReduction = (F,I,bound) -> (
    --checks that an ideal F is a reduction of an ideal I on an
    --ambient projective curve
    --by checking that FI^m = I^(m+1) locally at the minimal primes of I
    --with m up to the constant bound.
    P := primaryDecomposition radical I;
    t := all(P, p-> not isSubset(((F*I): I^2), p));-- true if F*I:is not in p
    count := 1;
    while (not t and count < bound) do(
              t = all(P, p-> not isSubset(((F*I^(count+1)): I^(count +2)), p));
	    count = count+1;
	    );
    t)

localMinimalReduction = method(Options => {Tries => 20, Check => false})
localMinimalReduction Ideal :=  Ideal => o -> I -> (
    --use Check => true over very small fields
    I' := trim I;
    if codim I' != 1 then error "expected codim 1 ideal";
    if numgens I' == 1 then return I' else (
	f := max((I'_*/degree)_0);
	F := ideal random(f, I');
       
        if o.Check == false then return F else(
            t :=isLocalMinimalReduction(F,I', 10);
            if t then F else(
    		count := o.Tries;
		while (count >0 and not t) do (
	    	    F = ideal random(f+1, I');
            	    t = isLocalMinimalReduction(F,I', 10);
	    	    count = count - 1
		                              );
        	if t then F else 
		error "couldn't find local minimal reduction")
		            )))
-*
linearSeries = method (Options => {Conductor=>null, 
	                          ConductorReduction => null, 
				  ShowBase => false,
				  Check => false})
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

    dsing := dim singularLocus R;
    if dsing <= 0 then (
	cond := ideal 1_R;
	condRed := 1_R) else(
        if o.Conductor === null then 
	    cond = conductor R else
	    cond = o.Conductor;
        if o.ConductorReduction === null then 
          condRed = localMinimalReduction(cond, Check => o.Check) else
          condRed = o.Conductor);
    --now cond is the conductor ideal of $R$, 
    --and condRed is a minimal reduction.
    base := saturate(D0sat*cond);
--    base := D0sat*condRed;--this is saturated*principal, so saturated
    F := ideal(base_*_0);
    f := degree F_0;
    A := F:base;    
    F == intersect(A,base);
    --Now  F~A + D0 + conductor
--    Aminus := saturate(A*Dinfsat*condRed);
--    Aminus := saturate(A*Dinfsat);    
    Aminus := saturate(A*Dinfsat*cond);    
--    Aminus := saturate(A*Dinfsat*condRed);    
    ls := gens image basis(f, Aminus);
error();
    if o.ShowBase == false then ls else (ls, Aminus)
)

*-


linearSeries = method(Options => {Conductor=>null, 
	                          ConductorReduction => null, 
				  ShowBase => false,
				  Check => false})

linearSeries (Ideal,Ideal) := Matrix => o-> (D0,Dinf)  ->(
    -- returns a matrix whose elements span the complete linear series 
    --|D0-Dinf|+base points,
    -- where D_0, Dinf \subset R
    -- are the ideals of effective divisors in the ring R = S of an ACM curve C0,
    -- with normalization C, eg a plane curve
    R := ring D0;
    --
    dsing := dim singularLocus R;
    if dsing <= 0 then 
	cond := ideal 1_R else
          if o.Conductor === null then 
	    cond = conductor R else
	         cond = o.Conductor;
    --
    base := saturate(D0*cond);
    F := ideal(base_*_0);
    --Now  F~ D0 + conductor + A
    A := F:base;
    f := degree F_0;
    baseplus := saturate(A*Dinf);
    ls := gens image basis(f, baseplus);
--error();
    if o.ShowBase == false then ls else (ls, baseplus)
)

linearSeries Ideal := Matrix => o -> D0 ->  (
    Dinf := ideal(1_(ring D0));
    linearSeries(D0, Dinf, o)
    )

///
--here--
restart
debug loadPackage( "PlaneCurveLinearSeries", Reload => true)
--two characteristic pairs
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
linearSeries p
--p should have 2 elements
L = for i from 0 to 6 list (rank source linearSeries (p^i)) 
assert(L == {1, 2, 3, 4, 5, 6, 7})
--

   kk = ZZ/19
   S = kk[x,y,z]
   setRandomSeed 0
   --
   I = kernel map(kk[s,t], S, {s^3, s^2*t,t^3})
   p = {1,0,0}; 
   o = {1,1,1}; 
   q = o
   C = S/I
   genus C
   geometricGenus C
   pC = fromCoordinates(p,C)
   linearSeries(pC^3) 
   --
   I = ideal"x3+y3+z3"
   p = {1,0,-1}
   q = {1,-1,0}
   o = {0,1,-1}
   C = S/I
   --
   for  i from 0 to 3 do << (q = addition(o,p,q,C))<<endl;
  Text
   so 9p ~ o.   
   --I don't like this!
   more primitively,

  Example
   pC = fromCoordinates(p,C)
   oC = fromCoordinates(o,C)
   qC = oC
   i = 2
   (ls,B) = linearSeries(pC^i,oC^(i-1),ShowBase =>true);
   ls--error-- this linear series has dim 4, should have dim 2
   
   netList   for i from 1 to 10 list(
   (ls,B) = linearSeries(pC^i,oC^(i-1),ShowBase =>true);
   p'C = select(primaryDecomposition ideal ls, J -> J:B != 1)
       )

///
addition = method()
addition(Ideal, Ideal,Ideal) := Ideal => (origin,p,q) ->(
    --Given the ideal of a plane curve of arithmetic genus 1,
    --with assigned origin o,
    --and two (smooth) points p,q, compute their sum.
    --the points are given as codimension 1, linear
    --ideals in the ring of the curve.
    E := ring p;
    if genus E != 1 or numgens E != 3 then
    	error"Needs points on a plane curve of arithmetic genus 1";
    I := ideal E;
    if codim origin != 1 then error"first point not on curve";
    if codim p != 1 then error"second point not on curve";
    if codim q != 1 then error"third point not on curve";    
    
    (ls, B) := linearSeries(p*q,origin, ShowBase => true);

    t := primaryDecomposition ideal ls;
    s := select(t/(I -> I:B), J -> J!= ideal 1_E);
    s_0
    )

addition (List, List, List, Ring) := List => (o, p , q, E) ->(
    --same but with numerical coordinates
    oE := fromCoordinates(o, E);    
    pE := fromCoordinates(p, E);
    qE := fromCoordinates(q, E);
    toCoordinates addition(oE,pE,qE)
    )

    
///
restart
loadPackage("PlaneCurveLinearSeries", Reload => true)
needsPackage "RandomPoints"
   kk = ZZ/19
   S = kk[x,y,z]
   I = ideal"x3+y3+z3"
   E = S/I
   (p,q,origin) = toSequence randomPoints (3,I)


multiples(10, p, origin)

p = fromCoordinates(p,E);
q = fromCoordinates(q,E);
for i from 0 to 10 do(
(ls,B) = linearSeries(p^(i+1),q^i, ShowBase => true);
sl = select((primaryDecomposition ideal ls)/(I -> I:B), 
    J -> J!= ideal 1_E);
s = sl_0;
<<(toCoordinates s)<<endl;
)


cycle = (p, origin) -> (
<< toCoordinates p<< endl;
(ls,B) = linearSeries(p^(i+1),origin^i, ShowBase => true);
sl = select((primaryDecomposition ideal ls)/(I -> I:B), 
    J -> J!= ideal 1_E);
s = sl_0;
<<toCoordinates s << endl;
while s != p do (i = i+1;
(ls,B) = linearSeries(p^(i+1),q^i, ShowBase => true);
sl = select((primaryDecomposition ideal ls)/(I -> I:B), 
    J -> J!= ideal 1_E);
s = sl_0;
<<toCoordinates s<<endl
)
)
cycle(p, origin)
///

///
restart
loadPackage"PlaneCurveLinearSeries"
S = ZZ/19[a,b,c]
mm = ideal gens S
sing = (ideal(a,b))^2
R = S/random(3, sing)
canonicalSeries R
///

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

projectiveImage Ideal := Ring => o -> D0 ->(
    projectiveImage(D0, ideal(1_(ring D0)), 
	              Conductor => o.Conductor))

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
canonicalImage Ideal := Ring => o -> I -> canonicalImage((ring I)/I)


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

   If E is a curve of arithmetic genus 1 with a marked smooth point o,
   then the map p -> O_E(p-o) is a map from the set of smooth points of E
   onto the Jacobian of invertible sheaves of degree 0,
   This makes the set of smooth points into a group with the operation
   p+r = q if, as divisors, p+r-o~q.
   The function @TO addition@, based on  @TO linearSeries@, 
   allows us to implement the group law.
   Here is an example with a smooth plane cubic:
  Example
   kk = QQ
   S = kk[x,y,z]
   p = {0,1,0}; pS = fromCoordinates(p,S)
   q = {1,0,0}; qS = fromCoordinates(q,S)
   o = {1,1,1}; oS = fromCoordinates(o,S)
   I = ideal random(3, intersect(oS, pS,qS))

   E = S/I   
   p = {0,1,0}; pE = fromCoordinates(p,E)
   q = {1,0,0}; qE = fromCoordinates(q,E)
   o = {1,1,1}; oE = fromCoordinates(o,E)

   r = addition(o,p,q, E)
  Text
   It is known that when one takes multiples of a point that is not torsion,
   the "height" - roughly the size of the coordinate - is squared
   with each iteraction, that is, the number of digits doubles:
  Example
   pp = addition(o,p,p,E)
   ppp = addition(o,pp,p,E)   
   pppp = addition(o,ppp,p,E)   
  Text
   On the other hand, over a finite field, a curve has only finitely many
   points, so any subgroup of the Jacobian is finite:
  Example
   kk = ZZ/19
   S = kk[x,y,z]
   p = {0,1,0}; pS = fromCoordinates(p,S)
   o = {1,1,1}; oS = fromCoordinates(o,S)
   setRandomSeed 0
   I = ideal random(3, intersect(pS,oS))
   E = S/I   
   geometricGenus E
   q = o
   netList ({o} | apply(25, i-> q = addition(o,p,q,E)))
  Text
   A cubic with a node or cusp is also arithmetic genus 1; in the case
   of a node, the smooth points are in correspondence with P^1 minus {0, infinity}
   and the Jacobian is the multiplicative troup of the field; in the case
   of a cusp the smooth points are in correspondence with P^1 minus {infinity},
   and the Jacobian is the additive group of the field:
  Example
   I = kernel map(kk[s,t], S, {s^3, s^2*t,t^3})
   C = S/I
   genus C
   geometricGenus C
  Text
   the singular point is the image of the point (0,1) in P^1,
   so we may take the origin to be the image of (1,1) and take
   another smooth point p to be the image of (1,0).
   
   The following example fails because B is contained in
   all the ideals in the primary decomposition. Perhaps
   because B is contained in the singular locus?
   Try taking the form F to be of one higher degree, or more random?
///
-*
  Example
   kk = ZZ/19
   S = kk[x,y,z]
   setRandomSeed 0
   p = {1,0,0}; 
   o = {1,1,1}; 
   q = o
   netList ({o}|apply(9, i-> q = addition(o,p,q,C)))
   netList ({o}|apply(9, i-> q = addition(o,q,p,C)))   
  Text
   so 9p ~ o.   
   --I don't like this!
   more primitively,
  Example
   pC = sub(pS,C)
   oC = sub(oS,C)  
   netList   for i from 1 to 9 list(
   (ls,B) = linearSeries(pC^i,oC^(i-1),ShowBase =>true);
   select(primaryDecomposition ideal ls, J -> J:B != 1)
       )
*-     


doc///
Key
 fromCoordinates
 (fromCoordinates, List, Ring)
 (fromCoordinates, ZZ, ZZ, ZZ, Ring)
Headline
 Compute the ideal of a point from its coordinates
Usage
 I = fromCoordinates(L,C)
 I = fromCoordinates(x,y,z, C)
Inputs
 L: List
  of three integers or field elements
 x: RingElement
 y: RingElement
 z: RingElement
  integer or field coordinates of a point on C (assumed to be a plane curve)
 C: Ring
  the ring in which the ideal of the point will be created
Outputs
 I: Ideal 
  of C, defining a point
Description
  Text 
   Convenient way to compute the ideal of a point on a plane curve,
   when the point is given by a list of its coordinates.
   If the coordinates are given as integers, they are
   interpreted as elements of the coefficient field
   The script returns an error if the point is not on the curve.
  Example
   S = ZZ/101[a,b,c]
   C = S/ideal"a3+b3-c3"
   P = {0,1,1}
   Q = {1,1,0}
   fromCoordinates(P,C)
   --fromCoordinates(Q,C) --would return an error.   
SeeAlso
 toCoordinates

///


doc ///
Key
 toCoordinates
 (toCoordinates, Ideal)
Headline
 coordinates of a point from its ideal
Usage
 L  = toCoordinates I
Inputs
 I: Ideal
  defining a point
Outputs
 L: List
  of elements of the ground field
Description
  Text
   This is the inverse of @TO fromCoordinates@
  Example
   S = ZZ/5[x,y,z]
   I = ideal(x- y, z)
   L = toCoordinates I
   I == fromCoordinates(L,S)
   
   S = GF(5,2,Variable => a)[x,y,z]/(ideal "x3-y3+z3")
   a^24 == 1
   (a^8)^3
   (a^16)^3
   p = {a^8, a^16, 0}
   fromCoordinates (p,S)
   L = toCoordinates fromCoordinates ({a^8,1,0}, S)
SeeAlso
 fromCoordinates
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

   If C is a general curve of genus 6, then C can be represented
   as a plane sextic with 4 nodes. Its canonical embedding is
   then the projective image of C by the space of cubic forms
   vanishing at the 4 nodes. This lies on the surface that is the
   image of P2 under the linear series consisting of the 
   cubics vanishing at the 4 nodes, a del Pezzo surface of
   degree 5.
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
   B' = gens image basis (3,nodes)
   B = sub(B',C0);
   canonicalSeries(C0) == B
  Text
   Now the image of C under B lies on the image of 
   P^2 under B'. Since "projective image defines a ring",
   we need to make sure the two ideals are in the same ring
   to compare them:
  Example
   X = projectiveImage B'
   C = projectiveImage B
   betti res ideal C
   betti res ideal X
   isSubset(sub(ideal X, ring ideal C), ideal C)
SeeAlso
 geometricGenus
 canonicalImage
///



doc///
Key
 canonicalImage
 (canonicalImage, Ring)
 (canonicalImage, Ideal)
 [canonicalImage, Conductor]
Headline
 canonical model of the normalization of a plane curve
Usage
 R' = canonicalImage R
 R' = canonicalImage I
Inputs
 R: Ring
   the homogeneous coordinate ring of a plane curve
 I: Ideal
   homogeneous ideal of a plane curve
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
   B' = gens image basis (3,intersect nodes)
  Text
   The ideal of nodes is the conductor, so
   the canonical series on C is the restriction of
   the set of cubics containing the nodes.
  Example
   B = sub(B',C);
   canC = projectiveImage B
   delPezzo = P5/ker(map(P2, P5, gens image basis (3,intersect nodes)))
   betti res ideal canC
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

doc///
Key
 ShowBase
Headline
 Option for @TO linearSeries@
Usage
 (ls,B) = geometricGenus(C,ShowBase => true)
Inputs
 C: Ring
Outputs
 ls: Matrix
  1xn matrix whose entres span the linear series plus basepoints
 B: Ideal 
  the base locus
Description
  Text
   The linear series computed for a plane curve is given as
   a matrix of forms of a certain degree in the ideal of the curve;
   Each form vanishes at a divisor PLUS a fixed locus, in common
   to all the forms but not necessarily equal to their intersection
   (unless the linear series to be computed is base-point free).
  Example
   C = ZZ/19[a,b,c]/(ideal"a5+b5-c5")
   geometricGenus C == 6
   p = fromCoordinates({0,1,1}, C)
   (ls, B) = linearSeries(p^6, p^3, ShowBase => true)
SeeAlso
 linearSeries
 fromCoordinates
///

doc ///
Key
 addition
 (addition, Ideal, Ideal, Ideal)
 (addition, List, List, List, Ring)
Headline
 addition on the smooth points of a genus 1 curve with chosen origin
Usage
 r = addition(p, q, origin)
 Lr = addition(Lp, Lq, Lorigin, C)
Inputs
 p: Ideal
 q: Ideal
 origin: Ideal 
  ideals of points on C
 Lp: List
 Lq: List
 Lorigin: List
  lists representing the coordinates of the points p,q,origin on C
 C: Ring
  homogeneous coordinate ring of a plane curve
Outputs
 r: Ideal
  of C = ring p
 Lr: List 
  of list of the coordinates of the sum
Description
  Text
   The elements of the Picard group of invertible sheaves
   of degree 0 on curve C of genus 1
   can be represented as O_C(p-origin) for smooth points
   p and any chosen smooth point origin; thus we may implement
   the group law 
   p+q = r from the linear equivalence relation of divisors
   p+q - origin ~ r.
  Example
   kk = ZZ/19
   S = kk[x,y,z]
   I = ideal"x3+y3+z3"
   E = S/I
   needsPackage "RandomPoints"
   (p,q,origin) = toSequence randomPoints (3,I)
   addition(p,q,origin, E)
   fromCoordinates(p,E)
SeeAlso
 linearSeries
 ShowBase
 toCoordinates
 fromCoordinates
///

-* Test section *-
TEST///
S = ZZ/101[a,b,c]
C = S/ideal"a3+b3-c3"
P = (0,1,1)
assert(fromCoordinates({0,1,1}, C) == ideal (a, - b + c))
///

TEST///
R = QQ[x,y,z]
I = fromCoordinates ({5,-3,9}, R)
assert({5,-3,9} == toCoordinates I)

///

TEST///
S = ZZ/32003[a,b,c]
I = ideal"a3+b3-c3"
p'= ideal(a,b-c)
assert(isSubset(I,p'))
R = S/I
p = sub(p',R)
assert (geometricGenus R == 1)
assert(canonicalSeries R == matrix{{1_R}})
linearSeries (p)
L = for d from 3 to 7 list rank source ((res ideal projectiveImage p^d).dd_(d-2))
assert(all(L, ell->ell == 1))
///

TEST///
setRandomSeed 27 -- with setRandomSeed 0 the generator of C6 factors!
S = QQ[x,y,z]
sing3 = (ideal(x,y))^3
sing1 = (ideal(x,z))^2
C4 = ideal random(5, sing3) -- quintic with ord 3-point; genus 3, hyperell.
C5 = ideal random(5, sing1) -- quintic with node, genus 5
C6 = ideal random(5, intersect(sing1, sing3))-- quintic with ord 3-point and a node; genus 2
assert (numcols canonicalSeries C4 == 3)
assert (numcols canonicalSeries C5 == 5)
assert (numcols canonicalSeries C6 == 2)
assert (geometricGenus C6 == 2)
///
 
TEST///
--two characteristic pairs
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
linearSeries p^2
L = for i from 0 to 6 list (rank source linearSeries (p^i)) 
assert(L == {1, 2, 3, 4, 5, 6, 7})
assert(degree projectiveImage p^3 == 3)
///

TEST///
setRandomSeed 0
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
canonicalSeries C3 == vars ((ring C3)/C3)

geometricGenus C1 == 0
geometricGenus C2 == 0
geometricGenus C3 == 3
geometricGenus C4 == 3
///

TEST///
--hyperelliptic curves. Note that with g>=6, the conductor computation fails.
S = ZZ/101[a,b,c]
q' = ideal(a,b)
p' = ideal(b,c)
g = 8
C = S/random(g+2, intersect (q'^g, p'))
--conductor C -- fails for g>=6
q = sub(q', C)
p = sub(p',C)
--geometricGenus C
assert(geometricGenus (C, Conductor => q^(g-1)) == 8)
--canonicalSeries C
assert(canonicalSeries (C, Conductor =>q^(g-1)) ==  
    sub(matrix" a7, a6b, a5b2, a4b3, a3b4, a2b5, ab6, b7", C))
--linearSeries(p^(g+2))
g = 2 -- 8 takes too long!
C = S/random(g+2, intersect (q'^g, p'))
--conductor C -- fails for g>=6
q = sub(q', C)
p = sub(p',C)
C' = projectiveImage (p^(2*g+1),Conductor =>q^(g-1))
assert (codim C' == max (keys minimalBetti(ideal C')/first))
assert(degree ideal canonicalImage (C,Conductor =>q^(g-1)) == g-1)
///

TEST///
   C = ZZ/19[a,b,c]/(ideal"a4+b4-c4")
   assert(geometricGenus C == 3)
   assert ((p = fromCoordinates({0,1,1}, C)) == ideal"a, c-b")
   (ls, B) = linearSeries(p^6, p^3, ShowBase => true)
   assert(saturate B == ideal(b^2-2*b*c+c^2, a*b-a*c))
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

--Here are many small examples; some should be in the docs, some
--in the TESTs, some deleted.

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

----to fix: why doesn't the canonical embedding lie on the del Pezzo?
restart
needsPackage "PlaneCurveLinearSeries"
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
   assert(conductor C0 == sub(nodes, C0))
   B' = gens image basis (3,nodes)
   B = sub(B',C0);
   assert(canonicalSeries(C0) == B)
   
   X = projectiveImage B'
   C = projectiveImage B
   betti res ideal C
   betti res ideal X
   assert(isSubset(sub(ideal X, ring ideal C), ideal C))
--but   
   isSubset(ideal X, sub(ideal C, ring ideal X)) -- fails


 


--The following fails -- apparently the particular seed
--leads to a reducible curve C6
    
setRandomSeed 0
S = QQ[x,y,z]
sing3 = (ideal(x,y))^3
sing1 = (ideal(x,z))^2
C4 = ideal random(5, sing3) -- quintic with ord 3-point; genus 3, hyperell.
C5 = ideal random(5, sing1) -- quintic with node, genus 5
C6 = ideal random(5, intersect(sing1, sing3))-- quintic with ord 3-point and a node; genus 2
netList decompose C6
conductor (S/C6)
degree singularLocus (S/C6)

--this succeeds
setRandomSeed 27
S = QQ[x,y,z]
sing3 = (ideal(x,y))^3
sing1 = (ideal(x,z))^2
C4 = ideal random(5, sing3) -- quintic with ord 3-point; genus 3, hyperell.
C5 = ideal random(5, sing1) -- quintic with node, genus 5
C6 = ideal random(5, intersect(sing1, sing3))-- quintic with ord 3-point and a node; genus 2
netList decompose C6
conductor (S/C6)
degree singularLocus (S/C6)

S = QQ
randomQQ = n -> sub(random (n*1000), QQ)/1000
randomQQ 100

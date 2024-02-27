--the following code succeeds with g=5 but not with g=6 or 7.
   g = 6
   S = ZZ/101[a,b,c]
   q' = ideal(a,b)
   p' = ideal(b,c)
   I = intersect(q'^g , p')
   C = S/(ideal random(g+2, I))
   integralClosure C

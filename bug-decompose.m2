E = QQ[a,b,c]/(ideal"a3+b3-c3")
I = ideal(b-c)
decompose I == {ideal (b - c, a)}
--but a is not in I:
gens (ideal a) % I
minimalPrimes I -- also wrong
primaryDecomposition I -- gives the right answer.

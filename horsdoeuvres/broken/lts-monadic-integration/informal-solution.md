# Informal solution

Write (c(\mu)) for the Pettis barycenter, characterized by
\[
 x^*(c(\mu))=\int_X x^*(x)\,d\mu(x)\qquad(x^*\in X^*).
\]
The hypothesis “enough Pettis integrals” supplies this point of (X) for
every measure in \(\mathbb M X\). The weak sigma-algebra makes (c)
measurable because every scalar composite (x^*\circ c) is the measurable
integration functional above; the norm bornology and the defining moment
bound for \(\mathbb M\) make (c) bornological.

For the unit, the barycenter of the Dirac measure is the point itself:
\(c(\delta_x)=x\), since every (x^*) takes the same value on both sides.
For multiplication, let \(\Xi\in\mathbb M\mathbb M X\). Pettis/Fubini
interchange gives, for every (x^*\in X^*),
\[
x^*\!\left(c(\mathbb M c(\Xi))\right)
=\int_{\mathbb M X}\!\int_Xx^*(x)\,d\mu(x)\,d\Xi(\mu)
=x^*\!\left(c(\operatorname{join}\Xi)\right).
\]
Continuous linear functionals separate points of a Banach space, so the two
barycenters agree. These are exactly the unit and associativity axioms for an
\(\mathbb M\)-algebra.

The stem does not define the particular measure monad or spell out “enough”;
a formal proof must import those definitions and their measurability,
bornology, and Pettis-Fubini lemmas. The algebraic proof above is conditional
on precisely those advertised hypotheses rather than on an invented model of
\(\mathbb M\).

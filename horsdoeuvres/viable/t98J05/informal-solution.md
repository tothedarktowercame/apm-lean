# Informal solution

The constant form \(5dx+dy\) is invariant under integer translations, so it
descends to (N\). It is closed, and pullback commutes with exterior
differentiation; hence (d\beta=p^*(d\alpha)=0\).

Choose a horizontal generator of (N) avoiding the finitely many points where
the quotient is not a covering. Its period under \(\alpha\) is (5). Lift it
from (M); if the first lift is not closed, traversing the generator twice
closes it because the covering degree away from those points is two. The
resulting closed curve has \(\beta\)-period (5) or (10), so \(\beta\)
cannot be exact.

Periods of \(\alpha\) define the homomorphism
\((m,n)\mapsto5m+n\) on \(H_1(N;\mathbb Z)\). The primitive class
\((1,-5)\) is nonzero and lies in its kernel, and it is represented by an
embedded essential circle on the torus. Take a closed lift (c) of a suitable
multiple of this circle to (M) (equivalently draw its preimage and choose a
component). Then
\[
 \int_c\beta=\int_{p\circ c}\alpha=0.
\]
Its image has nonzero homology class, so (c) cannot be null-homotopic.

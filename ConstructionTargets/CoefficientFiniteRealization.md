# Finite signed-chain realization with explicit coefficients

`finiteSingularChainRealize` sends a finitely supported integer-weighted
formula of continuous singular simplices to an R-linear morphism from
`ModuleCat.of R R` into actual singular chains. The ring `R`, space `X`
and family index type are universe zero. `R` is a commutative ring and
`X` is a topological space. Integer weights encode signed formulas; no
integral homology result or change-of-coefficients theorem is used.

The singleton and addition equations are proved directly for the finite
sum of coefficient-general singular generators. If every simplex in the
support lies in a member of an arbitrary subset family, then
`finiteSingularChainRealize_factors` constructs a morphism `q` into
`CoefficientSmallPath.coverSmallChains`. Its composite with the actual
`coverSmallInclusion` equals the realization. The proof inducts on the
finite formula, using the reviewed small-generator inclusion equation.
The family need not be open or cover X; nonemptiness and connectedness
are not assumed.

The interval example uses the continuous edges t/2 and (t+1)/2, contained
respectively in the two sets of `CoefficientSmallPath.intervalCover`.
The signed formula has weights +1 and -1. Both integer and rational
factorizations compile, with five printed axiom audits.

The Lean file is an exact promotion of `/tmp/CoefficientFiniteRealization.lean`,
SHA256 `de296b315978f3ddf6818d2c5e71a7eee15499bd75f74aaa0a9999d4660e8932`.

Identification with the reviewed subdivision and prism, their small-chain
restrictions and the inclusion-compatible restricted homotopy remain
downstream. No such identification, eventual smallness, homology comparison,
excision or frozen consumer closure is claimed here.

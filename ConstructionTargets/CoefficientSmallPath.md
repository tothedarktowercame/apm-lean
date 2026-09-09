# Finite small-path chains with explicit coefficients

The ring `R`, space `X` and cover index type are universe-zero types. The
ring is commutative and the space has an arbitrary topology. The path
construction takes indexed open sets covering `X` and a path from `x` to
`y`; no global nonemptiness or path-connectedness assumption is added.

`coverSmallChains` applies the actual simplicial singular-chain functor with
coefficient object `ModuleCat.of R R` to the cover-small simplicial set.
`coverSmallInclusion` is induced by its inclusion into all singular simplices.
`coverSmallGenerator` constructs a generator from a simplex whose range lies
in a specified cover member. `coverSmallGenerator_comp_ι` identifies its
image with the actual absolute singular generator.

`exists_small_path_edges` pulls the open cover back along the path and uses
finite subdivision of the unit interval. Each resulting subpath lies in a
cover member and therefore supplies a small singular edge. Its included
absolute boundary is the difference of the adjacent vertex generators.
`telescoping` sums these differences, and `exists_small_path_chain` explicitly
chooses the finite sum of the subordinate edge generators. The resulting
equation is `c ≫ inclusion.f 1 ≫ d 1 0 = vertex y - vertex x`.
This is an equation after the actual inclusion into absolute chains.

The rational and integral examples use the path from `0` to `1` in the real
line and the two-member cover `(-∞,1)` and `(0,∞)`. The open-cover proof and
both coefficient-specific boundary equations compile in the fixture.

The source exactly promotes `/tmp/CoefficientSmallPath.lean`, SHA256
`e498fec550ad3143da251193e524cdc126de5a5babdeb15dc6a562768ef742d7`.
Validation includes fixture and canonical compilation, the focused build,
five standard-only printed axiom audits including both interval examples,
and placeholder and scope checks.

The induced H0 inverse and its two inverse equations remain to be assembled.
Positive-degree comparison, relative excision and rational sphere H1/H2
remain downstream. This packet claims neither an H0 isomorphism nor frozen
consumer closure.

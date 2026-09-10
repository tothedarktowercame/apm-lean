# Relative small-chain comparison with explicit coefficients

This module constructs a relative comparison using actual subtype inclusion,
coefficient object `ModuleCat.of R R` and categorical cokernels. The
commutative ring R, topological space X and family index type are universe
zero. A is an arbitrary subset of X and need not be open. Map construction
and monicity require no cover assumption. The homology comparison requires
an indexed open cover of X, without connectedness, nonemptiness or finiteness.

`restrictedMap` applies the coefficient-general chain functor to the existing
restricted-cover simplicial map from A to X. Its generator equation,
differential compatibility and square with both actual small-chain inclusions
are proved. The actual subtype simplicial map is injective, which establishes
componentwise and chain-map monicity of `subspaceMap`. The inclusion square
then proves monicity of `restrictedMap`.

`relativeSmall` and `relativeChains` are the categorical cokernels of those
maps. `relativeMap` is induced by the two actual small-chain inclusions.
Absolute comparison on X and on A with its restricted cover discharges the
hypotheses of `CoefficientCokernelComparison`, giving `comparisonIso` in every
degree. `comparisonIso_hom` identifies its forward map with homologyMap of
`relativeMap`; both inverse laws are proved. `subspaceMap_eq_postcomposition`
identifies the target map with actual singular postcomposition by Subtype.val.
The imported `SingularExcision` supplies restricted-cover simplicial geometry;
no AddCommGrpCat conclusion is reinterpreted over R.

Integer and rational examples use the closed interval subtype [0,1] in the
overlapping real interval cover. Nine printed axiom audits are included.
The Lean file is an exact promotion of `/tmp/CoefficientRelativeSmall.lean`,
SHA256 `8d748371a567aff62b8214d511fb6275fd24832a9544540d21fb5d39c1bbfd79`.

Coefficient-general excision still needs subcomplex union/intersection and
actual-subspace quotient identifications. Sphere suspension and rational
S2 H1/H2 remain downstream. No excision or frozen consumer closure is claimed.

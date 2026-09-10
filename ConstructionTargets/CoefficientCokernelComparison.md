# Coefficient-general cokernel homology comparison

This module works in `ChainComplex (ModuleCat.{0} R) Nat` for a universe-zero
commutative ring R. It constructs the short complex of a chain map and its
actual categorical cokernel; monicity of that map proves short exactness.
A supplied commuting square `f ≫ b = a ≫ f'` induces `cokernelSquareMap`,
using the actual `cokernel.map` as its third component.

`cokernelSquare_homologyMap_isIso` assumes both horizontal maps f and f'
are monic. It explicitly requires homology isomorphisms for a and b in the
current degree i and every adjacent lower degree j with
`(ComplexShape.down Nat).Rel i j`. The generic homology-sequence comparison
then proves that the induced cokernel map is an isomorphism on homology.
`comparisonIso` assumes those absolute isomorphisms in all degrees and
constructs the cokernel-homology isomorphism in any chosen degree.

`comparisonIso_hom` identifies the forward arrow exactly with the homology
map of `cokernel.map`. `inverse_left` and `inverse_right` prove both inverse
laws. Integer and rational identity-square examples and five printed axiom
audits are included. Imports reuse `CoefficientSmallComparison` and Mathlib's
`HomologySequenceLemmas`.

The Lean file is an exact promotion of `/tmp/CoefficientCokernelComparison.lean`,
SHA256 `eaa11a983fd6cbd117026568e4eddd48be7911686d61513dc1ab2b2794f490ce`.

The geometric consumer must still construct the restricted-cover chain map,
prove its generator and inclusion equations and horizontal monicity, and
apply the reviewed absolute small-chain comparison on X and A. None of those
geometric hypotheses is discharged here. This module claims no geometric
relative comparison, excision or frozen consumer closure.

# Integral singular-homology coefficient comparison

`IntegralSingularHomologyComparison.lean` compares the two integral singular
homology constructions used in this repository: `ModuleCat ℤ` and
`AddCommGrpCat`.

The comparison is now natural, rather than merely an objectwise isomorphism.
The file proves:

- `singularChainsComparison_naturality`, by checking the square on each
  singular-simplex coproduct generator; and
- `singularHomologyComparison_naturality`, by combining that chain square
  with Mathlib's naturality theorem for homology preserved by the forgetful
  functor.

The homology theorem says that applying a continuous map in `ModuleCat ℤ` and
then forgetting agrees, through `singularHomologyComparison`, with applying
the native `AddCommGrpCat` singular-homology map. It is intended for consumers
such as the positive-dimensional antipodal sphere calculation, where the
geometric calculation is performed in `AddCommGrpCat` but the frozen statement
uses `ModuleCat ℤ`.

This target does not prove the antipodal sign. In particular, it does not
repair or close the frozen `t94J08` bridge, whose `n = 0` case asks for an
ordinary `H₀(S⁰; ℤ) ≅ ℤ` orientation and is therefore defective unless the
statement is restricted to positive dimensions or changed to reduced
homology.

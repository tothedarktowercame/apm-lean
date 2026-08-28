# Projective quotient exact splitting

This target packages the generic algebraic step needed by the `t96A03`
degree-two calculation.  For a short exact sequence

`0 ⟶ A ⟶ B ⟶ P ⟶ 0`

in an abelian category, if `P` is projective, projectivity factors `𝟙 P`
through the epic map `B ⟶ P`.  The resulting section and exactness give an
isomorphism `B ≅ A ⊞ P` via Mathlib's short-complex splitting API.

The main declarations are:

- `shortExactIsoBiprod`, the reusable short-exact categorical isomorphism;
- `exactIsoBiprod`, the equivalent consumer form taking exactness together
  with separate mono/epi instances;
- `projectiveSection` and `projectiveSection_comp`, exposing that its section
  is derived from projectivity rather than assumed;
- `fixtureShortExact` and `fixtureIso`, validating the result for
  `A = ℤ²` and `P = ℤ` in `ModuleCat ℤ`; Mathlib synthesizes projectivity from
  the free rank-one module instance.

This does not identify a `t96A03` geometric kernel, construct its exact
sequence, or claim the frozen result.  Those remain consumer-side obligations.

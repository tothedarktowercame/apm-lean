# Proof Outline: t94A08

## Closer hop 2

The earlier derivative proof from git history was restored and now proves the
first frozen conjunct as `apm_t94a08_regularLevelSet_quadratic1`.  The node
`[1:0:0]` was also constructed and proved to belong to `sigma2`, carefully
transporting through the noncanonical representative.

The two manifold conjuncts remain open.  Mathlib provides no local coordinate
charts for `Projectivization` equipped with this file's custom coinduced
topology.  Closing the positive conjunct requires constructing the conic's
local quotient charts (or a topological identification with the complex
projective line).  Closing the negative conjunct requires proving a local
topological obstruction for the crossing of its two branches.  The detailed
search boundary is recorded at the remaining `sorry` in `lean/Main.lean`.

The original regular-cone formalization was complete and sorry-free; the
repaired statement's separately topological manifold conjuncts remain partial.

## Closer hop 3

The degenerate conic's branch structure is now formal rather than descriptive.
`apm_t94a08_quadratic2_factor` proves
`z₁²+z₂²=(z₁+iz₂)(z₁-iz₂)`, and
`apm_t94a08_sigma2_eq_branches` identifies `sigma2` with the union of the two
corresponding homogeneous projective lines. The distinguished node is proved
to lie on both branches.

The negative manifold claim is consequently reduced to a local invariant of
this explicit crossing. The positive claim still requires projective quotient
charts for the smooth conic.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94A08.md`

## Formal proof

1. Bundle the derivative of `z₀² + z₁² + z₂²` as the continuous linear map
   `h ↦ 2 z₀h₀ + 2 z₁h₁ + 2 z₂h₂`, using the coordinate projections and
   `HasFDerivAt.pow`.
2. If this derivative were zero, evaluate it on each coordinate vector
   `Pi.single i 1`.  All three coordinates of `z` would vanish, contradicting
   `z ≠ 0`.  Hence the first conic satisfies the frozen regular-cone criterion.
3. For the second quadratic `z₁² + z₂²`, use `(1,0,0)`.  It is nonzero and lies
   on the cone, while the explicit Fréchet derivative there is zero.  This
   contradicts the regular-cone condition and proves the negated conjunct.

The proof uses Mathlib's `ContinuousLinearMap.proj`, `HasFDerivAt.pow`, and
`HasFDerivAt.add`; no projective-space smoothness theorem is needed because the
statement deliberately encodes smoothness through the affine-cone derivative.

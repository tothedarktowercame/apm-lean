# Proof Outline: t94A08

The Lean formalization is complete and sorry-free.

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

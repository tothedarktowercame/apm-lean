# Proof Outline: m97A02

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m97A02.md`

## Compiled progress

- Cosine maps `[0,1]` into itself and preserves the Dottie-number anchor.
- The derivative-only bound controls pointwise values of anchored functions.
- `apm_m97A02_sin_one_lt_one` proves the strict contraction constant required
  for composition by cosine.
- `apm_m97A02_cos_remainder_mul_sub` proves the scalar local-Lipschitz
  estimate for the differentiated sine remainder using global cosine
  Lipschitzness; this avoids a separate quadratic Taylor theorem.
- `apm_m97A02_derivWithin_sin_sub_self` proves the exact derivative formula
  for `sin ∘ x - x` throughout the closed interval.
- `apm_m97A02_derivWithin_remainder_sub_le` lifts the scalar estimate to the
  pointwise `derivWithin` estimate needed for the derivative supremum norm.

## Remaining boundary

- Prove `apm_m97A02_anchored_derivative_cauchy_complete`, whose exact Lean
  statement is recorded in the main boundary comment. It expresses
  completeness directly through derivative-sup Cauchy sequences and avoids
  presupposing the missing bundled normed type.
- Transport that theorem into a complete normed model of anchored `C¹`
  functions.
- Bundle composition by cosine as a bounded linear contraction.
- Use the compiled pointwise remainder estimate in that normed model and apply
  the inverse/fixed-point machinery.

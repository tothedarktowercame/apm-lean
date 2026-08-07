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

## Remaining boundary

- Construct and prove completeness of the anchored `C¹` derivative-norm space.
- Bundle composition by cosine as a bounded linear contraction.
- Lift the scalar remainder estimate through `derivWithin` chain/product rules
  and apply the inverse/fixed-point machinery.

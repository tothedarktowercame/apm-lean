# Proof Outline: a94J06

## Problem

Let γ denote the unit circle, oriented counterclockwise. For z ∉ γ,
evaluate ∫_γ ζ̄/(ζ-z) dζ as a function of z.

## Key Insight

The integrand involves ζ̄ (conjugation), which is **not holomorphic**.
The Cauchy integral formula does not apply directly.

**Trick:** On the unit circle |ζ| = 1, ζ̄ = 1/ζ (since ζ · ζ̄ = |ζ|² = 1).
This converts the antiholomorphic ζ̄ into a rational (meromorphic) function:

  ζ̄/(ζ-z) = 1/(ζ(ζ-z))

## Formal Proof Strategy

1. **Integrand rewrite** (`conj_eq_inv_on_circle`, `integrand_eq_rational`):
   On |ζ| = 1, ζ̄ = ζ⁻¹, so ζ̄/(ζ-z) = (ζ(ζ-z))⁻¹. Applied pointwise
   on the circle via `circleIntegral.integral_congr`.

2. **Partial fractions** (`partial_fractions`, `integral_partial_fractions`):
   (ζ(ζ-z))⁻¹ = z⁻¹((ζ-z)⁻¹ − ζ⁻¹), splitting the integral into two
   standard Cauchy kernels.

3. **Evaluation** via Mathlib circle integral API:
   - ∮ (ζ-w)⁻¹ dζ = 2πi when w inside disk (`integral_sub_inv_of_mem_ball`)
   - ∮ (ζ-w)⁻¹ dζ = 0 when w outside (`circleIntegral_eq_zero_of_differentiable_on_off_countable`)
   - ∮ ζ⁻¹ dζ = 2πi (`integral_sub_center_inv`)
   - ∮ ζ⁻² dζ = 0 (`integral_sub_zpow_of_ne`, since -2 ≠ -1)

## Results

| Case | Value | Theorem |
|------|-------|---------|
| \|z\| < 1, z ≠ 0 | 0 | `apm_a94J06_inside_nonzero` |
| z = 0 | 0 | `apm_a94J06_at_zero` |
| \|z\| < 1 (combined) | 0 | `apm_a94J06_inside` |
| \|z\| > 1 | -2πi/z | `apm_a94J06_outside` |

## z ∈ γ Case

For z on the circle, the integral is a divergent improper integral. Its
Cauchy principal value is -πi/z (Sokhotski-Plemelj). This case is outside
the scope of the present contour-integral formalization — Mathlib has no
principal value for contour integrals — so it is recorded only in the
informal proof.

## Closer Hop 1

The historical commit `6bbe1d7` proves the inside and outside evaluations but
predates the frozen boundary nonintegrability conjunct. Its foundational
rationalization has been ported as three compiled lemmas in the current file.
The first two conjuncts can be completed by porting its partial-fraction and
Cauchy-kernel calculations. The new boundary requires proving that multiplying
the pole by the nonvanishing conjugate numerator does not restore circle
integrability; no packaged transport theorem was found.

## Lean State

- **Sorry count:** 1
- **Classification:** partial
- **Validation:** `lake env lean problems/a94J06/lean/Main.lean` — succeeds

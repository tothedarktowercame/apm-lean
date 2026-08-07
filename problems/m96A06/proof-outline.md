# Proof Outline: m96A06

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96A06.md`

## Compiled progress

- Products of two `L²` representatives, the forcing pairing, and the weighted
  `L∞ × L² × L²` expression are proved integrable.
- `apm_m96a06_eLpNorm_weighted_le` proves the raw multiplier estimate
  `‖a*f‖₂ ≤ ‖a‖∞ * ‖f‖₂`.

## Remaining boundary

- package multiplication by the raw `L∞` coefficient as an operator on the
  quotient `Lp` space and identify its representative with `a*f`;
- combine it with `ContinuousLinearMap.lpPairing` to build the bounded
  bilinear form and forcing functional;
- prove coercivity, apply Mathlib's Lax–Milgram theorem, and establish the
  representative-level Fréchet derivative formula.

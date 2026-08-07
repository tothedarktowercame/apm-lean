# Proof Outline: m94A04

The frozen Lean theorem is present in `lean/Main.lean`. The exact cubic
remainder identity is now proved.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A04.md`

## Remaining boundary

- use heterogeneous `Lp` multiplication to construct `f²`, `f³`, and
  `f²h` at the appropriate exponents;
- downgrade `L^(8/3)` and `L^(8/3)` remainder terms to `L²` on the finite
  interval;
- package `h ↦ 3f²h` as a quotient-level `LinearMap`;
- combine the exact remainder identity with `Lp.norm_smul_le` and ENNReal
  arithmetic to prove the epsilon-delta estimate.

Mathlib's `MeasureTheory.Function.Holder` already handles quotient-level
representative independence and Hölder norm bounds. No searched sibling
assembles the required exponent chain and derivative package.

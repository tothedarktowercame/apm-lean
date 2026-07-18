# Proof Outline: a94J05

## Problem

**(a)** If `f` is entire and bounded, then `f` is constant (Liouville's theorem).
**(b)** If `f` is entire and `Re(f)` is bounded below, then `f` is constant.

## Proof Strategy

**(a)** Direct application of Mathlib's `Differentiable.exists_const_forall_eq_of_bounded`
(Liouville's theorem, proved via Cauchy estimates in `Mathlib.Analysis.Complex.Liouville`).

**(b)** Exponential trick: define `g(z) = exp(-f(z))`.
- `g` is entire (composition of `exp` with `-f`).
- `|g(z)| = exp(-Re f(z)) ≤ exp(C)` since `Re f(z) ≥ -C`.
- By Liouville (part a), `g` is constant: `g(z) = g(0)`.
- So `exp(-f(z)) = exp(-f(0))`, giving `f(z) - f(0) ∈ 2πiℤ` for all z.
- The function `s ↦ f(s·z)` is continuous on `[0,1]`, and `‖f(s·z) - f(0)‖ ∈ {0, 2π, 4π, ...}`.
- By IVT: if `f(z) ≠ f(0)`, there exists `s₀` with `‖f(s₀·z) - f(0)‖ = π`, contradiction.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 1 (on part b IVT argument)
- **Classification**: partial
- **Proved**:
  - Part (a) `liouville_bounded`: complete, zero sorry
  - Part (b) `liouville_re_bounded_below`: exponential trick + Liouville + exp_eq_exp_iff_exists_int all proved; IVT step is the sorry boundary
- **Blocker**: The final IVT step requires showing that `‖f(s·z) - f(0)‖` is continuous in `s` and takes values in `{0, 2π, 4π, ...}`, leading to a contradiction via IVT when `f(z) ≠ f(0)`. The IVT itself is in Mathlib but connecting it to the complex arithmetic and norm computation needs careful plumbing.

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
- Since `g` is constant, its derivative is zero. The chain rule gives
  `exp(-f(z)) * (-f'(z)) = 0` for every `z`.
- The complex exponential never vanishes, so `f'(z) = 0` everywhere.
- Apply `is_const_of_deriv_eq_zero` to conclude that `f` is constant.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 0
- **Classification**: complete
- **Proved**:
  - Part (a) `liouville_bounded`: complete, zero sorry
  - Part (b) `liouville_re_bounded_below`: complete, zero sorry; uses the
    derivative of the constant exponential and `Complex.exp_ne_zero`
- **Blocker**: none

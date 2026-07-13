# Proof Outline: a00J05

## Problem

Let K ⊆ ℝ be a compact set with positive Lebesgue measure. Define
f(z) = ∫_K 1/(t-z) dm(t).

(a) Prove f is holomorphic on ℂ \ K.
(b) Prove f cannot be extended by analytic continuation to an entire function.
(c) Show lim_{|z|→∞} zf(z) exists and determine its value.

## Harvest Mismatch Note

The informal-solution file `apm-a00J05.md` was harvested with the **wrong
content**: it contains the proof for a00J04 (polynomial lemniscate), not a00J05
(Cauchy transform). The Lean statements in that file are entirely for the
lemniscate problem. This bundle implements the correct problem statement from
`a00J05.tex`.

## Answers

- **Part (c):** lim_{|z|→∞} zf(z) = -m(K), where m is Lebesgue measure.
  (Write z/(t-z) = -1 + t/(t-z); the second term vanishes under the integral.)

- **Part (b):** If f extended to entire g, then g(z) ~ -m(K)/z → 0 as z → ∞.
  By Liouville's theorem, g ≡ 0. But zf(z) → -m(K) ≠ 0, contradiction.

## Formalization Strategy

### Part (a): f holomorphic on ℂ \ K

Use differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The core derivative
computation `d/dz[1/(t-z)] = 1/(t-z)²` is **proved** in
`hasDerivAt_integrand`. The theorem assembly requires threading
measurability/integrability conditions through Mathlib's parametric integral
framework.

### Part (c): zf(z) → -m(K)

Split zf(z) = ∫_K (-1 + t/(t-z)) dm = -m(K) + ∫_K t/(t-z) dm. The second
integral is bounded by R·m(K)/(|z|-R) where K ⊆ [-R,R], hence → 0.

### Part (b): f not extendable to entire

Follows from (c) + Liouville: `Differentiable.apply_eq_of_tendsto_cocompact`.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 4 (the four main theorems)
- **Proved lemma**: `hasDerivAt_integrand` (the core derivative computation)
- **Classification**: partial

## Statement Repair

The proposed Lean statements from the informal proof file are for the wrong
problem (a00J04). This file implements the correct problem (Cauchy transform)
with the correct three-part structure. The answer to part (c) is `-m(K)`,
determined from the integral analysis.

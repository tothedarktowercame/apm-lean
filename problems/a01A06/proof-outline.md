# Proof Outline: a01A06

## Problem

Let `g : [0,1] → ℝ` be nonneg with `g ∈ L¹`. Suppose `∫ gf < A` whenever `∫ e^f ≤ 1`.

(a) What can you say about `m({g > λ})` for large `λ`?
(b) Can you conclude `g ∈ L²`?

## Answer

**(a)** `m({g > λ})` decays at least exponentially: `m({g > λ}) ≤ C·e^{-αλ}` for
some `C, α > 0`. The proof uses the test function `f = c·χ_E - log(e^c·m(E) + 1 - m(E))`
with `E = {g > λ}` and `c = λ/2`.

**(b)** Yes, `g ∈ L²`. From the exponential decay and the layer-cake formula
`∫g² = ∫₀^∞ 2λ·m({g>λ}) dλ`, the integral converges since `∫₀^∞ λ·e^{-αλ} dλ < ∞`.

## Lean formalization status

**Classification: partial** (4 sorries, 0 errors)

The Lean file formalizes the mathematical structure faithfully:
- `OrliczBound` structure correctly captures the hypothesis
- `distribution_exponential_decay` states part (a) with `ENNReal.ofReal`
- `orlicz_bound_implies_L2` states part (b)
- `test_function_admissible` isolates the key computational lemma
- `exponential_decay_implies_L2` isolates the layer-cake bridge

### Statement repairs applied

1. Added `Measurable g` to the hypothesis (required for distribution function)
2. Changed `A` from `ℝ≥0` to `ℝ` for consistency with the integral bound
3. Added `0 < A` hypothesis (nontrivial bound)
4. Added `IntegrableOn (fun x => g x * f x)` as an explicit hypothesis for `bound`
5. Used `ENNReal.ofReal` instead of `NNReal.toENNReal` (correct Mathlib API)

### Blockers

The core analytical arguments require Mathlib infrastructure that is not
straightforward to apply:

1. **Test function admissibility** (`test_function_admissible`): requires
   integration of `e^{c·χ_E}` over `[0,1]` decomposed into `E` and `E^c`,
   using `setIntegral_const` and indicator decomposition. Elementary
   computation but needs several glue lemmas.

2. **Distribution decay** (`distribution_exponential_decay`): the optimization
   argument (choosing `c = λ/2`, deriving implicit inequality, solving for
   `m({g>λ})`) requires distribution function manipulation and integration
   over level sets beyond current Mathlib API.

3. **Layer-cake / Cavalieri** (`orlicz_bound_implies_L2`,
   `exponential_decay_implies_L2`): `lintegral_norm_eq_lintegral_meas_lt`
   exists in Mathlib but requires careful ENNReal setup for `g²` over `[0,1]`.

## Files

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a01A06.md`
- Lean attempt: `lean/Main.lean`

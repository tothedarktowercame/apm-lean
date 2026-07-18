# Proof Outline: a94A05

## Problem

**(a)** Let `A` be an arbitrary collection of open subintervals of a bounded
interval `I` in `ℝ`. Prove that `A` includes a sequence of pairwise disjoint
intervals `I₁, I₂, ...` such that the union `U = ⋃ A` is contained in
`⋃ⱼ I'ⱼ`, where `I'ⱼ` is concentric with `Iⱼ` but five times as long.

**(b)** Let `f : I → ℝ` be arbitrary, `C = {x ∈ I : f is differentiable at x and f'(x) = 0}`.
Show that `f(C)` has Lebesgue measure zero.

## Statement Repair

The proposed Lean statements in the informal proof had several structural issues:

1. **`inflate5` definition was wrong:** used `5 * r / 2` giving 5/2× length instead of 5×.
2. **Part (a) return type `ℕ → Set ℝ`** with `S k = ∅` padding does not faithfully express
   "a disjoint subcollection." Mathlib's subfamily `u ⊆ t` with `u.PairwiseDisjoint` is correct.
3. **Part (b) via direct Vitali argument** is unnecessary: Mathlib already provides
   `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (Sard's lemma for `E → E`),
   which applies directly to `E = ℝ` with `det = 0 ⟺ deriv = 0`.

## Proof Strategy

### Part (a): Vitali covering lemma (factor 5)

Applied Mathlib's `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`
with `τ = 5 > 3`. This gives a disjoint subfamily `u ⊆ t` of closed balls such that
every ball in `t` is contained in a 5× enlargement of some ball in `u`.

### Part (b): 1D Sard lemma (image of critical set has measure zero)

Applied Mathlib's `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`
(Sard's lemma: if `f : E → E` has Fréchet derivative with zero determinant on a set,
the image has measure zero). For `E = ℝ`:

- `volume` = additive Haar measure on `ℝ` (`addHaarMeasure_eq_volume`).
- `DifferentiableAt ℝ f x` → `HasFDerivAt f (fderiv ℝ f x) x` → `HasFDerivWithinAt ... C`.
- `deriv f x = 0` → `(fderiv ℝ f x) 1 = 0` (via `fderiv_apply_one_eq_deriv`) →
  `fderiv ℝ f x = 0` (1D linear map sending 1 to 0 is zero) → `det = 0`.

## Lean State

- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 0
- **Classification**: complete
- **Key lemmas used**:
  - `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall` (part a)
  - `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` (part b, Sard's lemma)

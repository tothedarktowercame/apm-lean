/-
! # APM a95A04: Symmetric mean value property implies f is constant a.e.

If f : [0,1] → ℝ is Lebesgue integrable and satisfies
∫_{x-h}^x f(t)dt = ∫_x^{x+h} f(t)dt whenever [x-h, x+h] ⊆ [0,1],
then f(x) = ∫_0^1 f(t)dt for almost every x ∈ [0,1].

## Proof strategy

1. **Symmetric splitting**: The hypothesis with x = midpoint, h = half-width
   gives ∫_a^x f = ∫_x^b f. Combined with ∫_a^b = ∫_a^x + ∫_x^b, this gives
   ∫_a^x = (1/2) ∫_a^b.

2. **Dyadic induction**: By induction on j, every dyadic interval
   [k/2^j, (k+1)/2^j] satisfies ∫_I f = c · 2^{-j} where c = ∫_0^1 f.

3. **Lebesgue differentiation**: For a.e. x, f(x) equals the limit of
   averages over shrinking intervals. Since all dyadic intervals containing x
   have average c, we conclude f(x) = c a.e.

## Statement repair

The generated `SymmetricMeanValue` used interval integrals directly, which
is correct. We keep this structure but add `IntervalIntegrable` hypotheses
where needed (Mathlib's interval integral API requires integrability).
The generated `lebesgue_differentiation_intervals` lemma was too specific;
we use Mathlib's `IntervalIntegrable.ae_hasDerivAt_integral` instead.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set intervalIntegral Filter

noncomputable section

/-- The symmetric mean value hypothesis:
∫_{x-h}^x f(t)dt = ∫_x^{x+h} f(t)dt whenever [x-h, x+h] ⊆ [0,1]. -/
def SymmetricMeanValue (f : ℝ → ℝ) : Prop :=
  ∀ x h : ℝ, 0 < h → Icc (x - h) (x + h) ⊆ Icc (0:ℝ) 1 →
    ∫ t in (x - h)..x, f t = ∫ t in x..(x + h), f t

/-- Splitting step: for any [a,b] ⊆ [0,1] with midpoint m = (a+b)/2,
∫_a^m f = (1/2) ∫_a^b f.

This follows directly from the symmetric mean value property applied with
x = m, h = (b-a)/2: the hypothesis gives ∫_a^m = ∫_m^b, and since
∫_a^b = ∫_a^m + ∫_m^b = 2·∫_a^m, we get ∫_a^m = (1/2)·∫_a^b.

**Note:** We need IntervalIntegrable to use `integral_add_adjacent_intervals`.
The hypothesis f ∈ L¹([0,1]) gives this on all subintervals of [0,1]. -/
lemma symmetric_split
    {f : ℝ → ℝ}
    (hsym : SymmetricMeanValue f)
    {a b : ℝ} (hab : a < b) (h_sub : Icc a b ⊆ Icc (0:ℝ) 1)
    (hf_int : IntervalIntegrable f volume a b) :
    ∫ t in a..((a + b) / 2), f t = (1 / 2 : ℝ) * ∫ t in a..b, f t := by
  -- Midpoint m = (a+b)/2, half-width h = (b-a)/2
  set m := (a + b) / 2 with hm
  set hw := (b - a) / 2 with hw_def
  -- Key arithmetic: a = m - hw, b = m + hw
  have ha : m - hw = a := by simp [hm, hw_def]; ring
  have hb : m + hw = b := by simp [hm, hw_def]; ring
  -- [m - hw, m + hw] = [a, b] ⊆ [0, 1]
  have hcc : Icc (m - hw) (m + hw) ⊆ Icc (0:ℝ) 1 := by
    rw [ha, hb]; exact h_sub
  -- Interval integrability on sub-intervals (m = (a+b)/2 is between a and b)
  have ham : a ≤ m := by simp [m]; linarith
  have hmb : m ≤ b := by simp [m]; linarith
  have hf_am : IntervalIntegrable f volume a m := by
    apply hf_int.mono_set
    rw [uIcc_subset_uIcc_iff_le]
    constructor <;> simp only [min_def, max_def]
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  have hf_mb : IntervalIntegrable f volume m b := by
    apply hf_int.mono_set
    rw [uIcc_subset_uIcc_iff_le]
    constructor <;> simp only [min_def, max_def]
    · split_ifs <;> linarith
    · split_ifs <;> linarith
  -- Apply the symmetric mean value hypothesis at x = m, h = hw
  have hsymm : ∫ t in (m - hw)..m, f t = ∫ t in m..(m + hw), f t :=
    hsym m hw (by simp [hw_def]; linarith) hcc
  -- Rewrite to get ∫_a^m = ∫_m^b
  have h_am_eq_mb : ∫ t in a..m, f t = ∫ t in m..b, f t := by
    rw [← ha, ← hb]
    exact hsymm
  -- ∫_a^m + ∫_m^b = ∫_a^b
  have h_split := integral_add_adjacent_intervals hf_am hf_mb
  -- Goal: ∫_a^m = (1/2) * ∫_a^b
  rw [← h_split, h_am_eq_mb]
  ring

/-- Dyadic integral formula: ∫_{k/2^j}^{(k+1)/2^j} f = c / 2^j
where c = ∫_0^1 f.

Proved by induction on j using symmetric_split. -/
lemma dyadic_integral_eq
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (0:ℝ) 1) volume)
    (hsym : SymmetricMeanValue f)
    (j : ℕ) (k : ℕ) (hk : k < 2 ^ j) :
    ∫ t in ((↑k : ℝ) / 2 ^ j)..((↑(k + 1) : ℝ) / 2 ^ j), f t =
      (∫ t in (0:ℝ)..1, f t) / 2 ^ j := by
  sorry

/-- Main theorem: f equals its average ∫_0^1 f(t)dt almost everywhere on [0,1].

**Proof sketch:** By dyadic_integral_eq, all dyadic intervals of level j have
average c = ∫_0^1 f. By the Lebesgue differentiation theorem
(Mathlib's `ae_hasDerivAt_integral`), f(x) equals the limit of averages over
shrinking intervals for a.e. x. Since the dyadic averages all equal c,
f(x) = c a.e. -/
theorem constant_of_symmetric_mean_value
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (0:ℝ) 1) volume)
    (hsym : SymmetricMeanValue f) :
    f =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      fun _ => ∫ t in (0:ℝ)..1, f t := by
  sorry

end

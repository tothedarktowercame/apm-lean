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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

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
  induction j generalizing k with
  | zero =>
      have hk0 : k = 0 := by simpa using hk
      subst k
      norm_num
  | succ j ih =>
      rcases k.even_or_odd' with ⟨q, hq | hq⟩
      · subst k
        have hq_lt : q < 2 ^ j := by
          rw [pow_succ] at hk
          omega
        have hparent := ih q hq_lt
        have hpow_pos : (0 : ℝ) < 2 ^ j := by positivity
        have hab :
            (q : ℝ) / 2 ^ j < ((q + 1 : ℕ) : ℝ) / 2 ^ j := by
          apply div_lt_div_of_pos_right _ hpow_pos
          norm_num
        have hsub :
            Icc ((q : ℝ) / 2 ^ j) (((q + 1 : ℕ) : ℝ) / 2 ^ j) ⊆
              Icc (0 : ℝ) 1 := by
          intro x hx
          constructor
          · exact le_trans (by positivity) hx.1
          · calc
              x ≤ ((q + 1 : ℕ) : ℝ) / 2 ^ j := hx.2
              _ ≤ 1 := by
                rw [div_le_one hpow_pos]
                exact_mod_cast Nat.succ_le_iff.mpr hq_lt
        have hf_parent :
            IntervalIntegrable f volume
              ((q : ℝ) / 2 ^ j) (((q + 1 : ℕ) : ℝ) / 2 ^ j) := by
          apply IntegrableOn.intervalIntegrable
          rw [uIcc_of_le hab.le]
          exact hf.mono_set hsub
        have hleft := symmetric_split hsym hab hsub hf_parent
        rw [hparent] at hleft
        have hstart :
            ((2 * q : ℕ) : ℝ) / 2 ^ (j + 1) = (q : ℝ) / 2 ^ j := by
          push_cast
          rw [pow_succ]
          field_simp
        have hend :
            (((2 * q + 1 : ℕ) : ℝ) / 2 ^ (j + 1)) =
              (((q : ℝ) / 2 ^ j + ((q + 1 : ℕ) : ℝ) / 2 ^ j) / 2) := by
          push_cast
          rw [pow_succ]
          field_simp
          ring
        rw [hstart, hend]
        calc
          (∫ t in (q : ℝ) / 2 ^ j..
              ((q : ℝ) / 2 ^ j + ((q + 1 : ℕ) : ℝ) / 2 ^ j) / 2, f t) =
              (1 / 2 : ℝ) * ((∫ t in (0 : ℝ)..1, f t) / 2 ^ j) := hleft
          _ = (∫ t in (0 : ℝ)..1, f t) / 2 ^ (j + 1) := by
            rw [pow_succ]
            ring
      · subst k
        have hq_lt : q < 2 ^ j := by
          rw [pow_succ] at hk
          omega
        have hparent := ih q hq_lt
        have hpow_pos : (0 : ℝ) < 2 ^ j := by positivity
        have hab :
            (q : ℝ) / 2 ^ j < ((q + 1 : ℕ) : ℝ) / 2 ^ j := by
          apply div_lt_div_of_pos_right _ hpow_pos
          norm_num
        have hsub :
            Icc ((q : ℝ) / 2 ^ j) (((q + 1 : ℕ) : ℝ) / 2 ^ j) ⊆
              Icc (0 : ℝ) 1 := by
          intro x hx
          constructor
          · exact le_trans (by positivity) hx.1
          · calc
              x ≤ ((q + 1 : ℕ) : ℝ) / 2 ^ j := hx.2
              _ ≤ 1 := by
                rw [div_le_one hpow_pos]
                exact_mod_cast Nat.succ_le_iff.mpr hq_lt
        have hf_parent :
            IntervalIntegrable f volume
              ((q : ℝ) / 2 ^ j) (((q + 1 : ℕ) : ℝ) / 2 ^ j) := by
          apply IntegrableOn.intervalIntegrable
          rw [uIcc_of_le hab.le]
          exact hf.mono_set hsub
        have hleft := symmetric_split hsym hab hsub hf_parent
        rw [hparent] at hleft
        have hsymm :
            (∫ t in (q : ℝ) / 2 ^ j..
                ((q : ℝ) / 2 ^ j + ((q + 1 : ℕ) : ℝ) / 2 ^ j) / 2, f t) =
              ∫ t in
                ((q : ℝ) / 2 ^ j + ((q + 1 : ℕ) : ℝ) / 2 ^ j) / 2..
                ((q + 1 : ℕ) : ℝ) / 2 ^ j, f t := by
          let m :=
            ((q : ℝ) / 2 ^ j + ((q + 1 : ℕ) : ℝ) / 2 ^ j) / 2
          let hw :=
            (((q + 1 : ℕ) : ℝ) / 2 ^ j - (q : ℝ) / 2 ^ j) / 2
          have hm_sub : m - hw = (q : ℝ) / 2 ^ j := by
            dsimp [m, hw]
            ring
          have hm_add : m + hw = ((q + 1 : ℕ) : ℝ) / 2 ^ j := by
            dsimp [m, hw]
            ring
          have hs := hsym m hw (by dsimp [hw]; linarith) (by
            rw [hm_sub, hm_add]
            exact hsub)
          simpa only [m, hm_sub, hm_add] using hs
        have hright :
            ∫ t in
                (((q : ℝ) / 2 ^ j +
                  ((q + 1 : ℕ) : ℝ) / 2 ^ j) / 2)..
                (((q + 1 : ℕ) : ℝ) / 2 ^ j), f t =
              (∫ t in (0 : ℝ)..1, f t) / 2 ^ (j + 1) := by
          rw [← hsymm, hleft, pow_succ]
          ring
        have hstart :
            (((2 * q + 1 : ℕ) : ℝ) / 2 ^ (j + 1)) =
              (((q : ℝ) / 2 ^ j + ((q + 1 : ℕ) : ℝ) / 2 ^ j) / 2) := by
          push_cast
          rw [pow_succ]
          field_simp
          ring
        have hend :
            (((2 * q + 1 + 1 : ℕ) : ℝ) / 2 ^ (j + 1)) =
              ((q + 1 : ℕ) : ℝ) / 2 ^ j := by
          push_cast
          rw [pow_succ]
          field_simp
          ring
        rw [hstart, hend]
        exact hright

/-- The primitive agrees with the affine function of slope `∫₀¹ f` at every
dyadic point of `[0,1]`. -/
lemma integral_zero_to_dyadic_eq
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (0 : ℝ) 1) volume)
    (hsym : SymmetricMeanValue f)
    (j k : ℕ) (hk : k ≤ 2 ^ j) :
    ∫ t in (0 : ℝ)..((k : ℝ) / 2 ^ j), f t =
      (k : ℝ) * (∫ t in (0 : ℝ)..1, f t) / 2 ^ j := by
  let a : ℕ → ℝ := fun n => (n : ℝ) / 2 ^ j
  have hpow_pos : (0 : ℝ) < 2 ^ j := by positivity
  have hint : ∀ n < k, IntervalIntegrable f volume (a n) (a (n + 1)) := by
    intro n hn
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le (div_le_div_of_nonneg_right (by norm_num) hpow_pos.le)]
    apply hf.mono_set
    intro x hx
    constructor
    · exact le_trans (by positivity) hx.1
    · calc
        x ≤ ((n + 1 : ℕ) : ℝ) / 2 ^ j := hx.2
        _ ≤ 1 := by
          rw [div_le_one hpow_pos]
          exact_mod_cast le_trans (Nat.succ_le_iff.mpr hn) hk
  have hsum := sum_integral_adjacent_intervals (f := f) (μ := volume) hint
  have hcells :
      ∀ n ∈ Finset.range k,
        (∫ t in a n..a (n + 1), f t) =
          (∫ t in (0 : ℝ)..1, f t) / 2 ^ j := by
    intro n hn
    simpa [a] using dyadic_integral_eq hf hsym j n (lt_of_lt_of_le (Finset.mem_range.1 hn) hk)
  have ha0 : a 0 = 0 := by simp [a]
  have hak : a k = (k : ℝ) / 2 ^ j := by rfl
  conv_lhs => rw [← ha0, ← hak]
  rw [← hsum]
  calc
    (∑ n ∈ Finset.range k, ∫ t in a n..a (n + 1), f t) =
        ∑ _n ∈ Finset.range k, (∫ t in (0 : ℝ)..1, f t) / 2 ^ j :=
      Finset.sum_congr rfl hcells
    _ = (k : ℝ) * (∫ t in (0 : ℝ)..1, f t) / 2 ^ j := by
      simp
      ring

/-- Continuity of the primitive extends its dyadic formula to the whole unit
interval. -/
lemma integral_zero_to_eq_mul
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (0 : ℝ) 1) volume)
    (hsym : SymmetricMeanValue f)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..x, f t = x * ∫ t in (0 : ℝ)..1, f t := by
  let k : ℕ → ℕ := fun n => ⌊x * (2 : ℝ) ^ n⌋₊
  let d : ℕ → ℝ := fun n => (k n : ℝ) / 2 ^ n
  have hk_le (n : ℕ) : k n ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    dsimp [k]
    calc
      x * (2 : ℝ) ^ n ≤ 1 * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hx.2 (by positivity)
      _ = ((2 ^ n : ℕ) : ℝ) := by norm_num
  have hd_mem (n : ℕ) : d n ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
    · rw [div_le_one (by positivity : (0 : ℝ) < 2 ^ n)]
      exact_mod_cast hk_le n
  have hd_le (n : ℕ) : d n ≤ x := by
    have hxn : 0 ≤ x * (2 : ℝ) ^ n :=
      mul_nonneg hx.1 (by positivity)
    have := Nat.floor_le hxn
    dsimp [d, k]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
    simpa [mul_comm] using this
  have hx_lt (n : ℕ) : x < d n + (1 / 2 : ℝ) ^ n := by
    have h := Nat.lt_floor_add_one (x * (2 : ℝ) ^ n)
    dsimp [d, k]
    calc
      x = (x * (2 : ℝ) ^ n) / 2 ^ n := by field_simp
      _ < (↑⌊x * (2 : ℝ) ^ n⌋₊ + 1) / 2 ^ n :=
        (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ n)).2 h
      _ = ↑⌊x * (2 : ℝ) ^ n⌋₊ / 2 ^ n + (1 / 2 : ℝ) ^ n := by
        rw [add_div]
        congr 1
        simpa only [one_div] using (inv_pow (2 : ℝ) n).symm
  have hd_tendsto : Tendsto d atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1))
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hd_le n))]
    linarith [hx_lt n]
  have hd_within : Tendsto d atTop (nhdsWithin x (Icc (0 : ℝ) 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hd_tendsto, Eventually.of_forall hd_mem⟩
  have hprim_tendsto :
      Tendsto (fun n => ∫ t in (0 : ℝ)..d n, f t) atTop
        (nhds (∫ t in (0 : ℝ)..x, f t)) :=
    ((intervalIntegral.continuousOn_primitive_interval
      (a := (0 : ℝ)) (b := 1)
      (by simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hf)) x
        (by simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx)).tendsto.comp
      (by simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hd_within)
  have haff_tendsto :
      Tendsto (fun n => d n * ∫ t in (0 : ℝ)..1, f t) atTop
        (nhds (x * ∫ t in (0 : ℝ)..1, f t)) :=
    hd_tendsto.mul_const _
  apply tendsto_nhds_unique hprim_tendsto
  convert haff_tendsto using 1
  funext n
  simpa [d, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    integral_zero_to_dyadic_eq hf hsym n (k n) (hk_le n)

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
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
  have hf_int : IntervalIntegrable f volume (0 : ℝ) 1 := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hf
  filter_upwards [hf_int.ae_hasDerivAt_integral, Measure.ae_ne volume (0 : ℝ),
    Measure.ae_ne volume (1 : ℝ)] with x hder hx0 hx1 hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  have hprimitive :
      HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, f t) (f x) x := by
    apply hder
    · simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    · simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
        (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have heq :
      (fun y => ∫ t in (0 : ℝ)..y, f t) =ᶠ[nhds x]
        (fun y => y * ∫ t in (0 : ℝ)..1, f t) := by
    filter_upwards [Icc_mem_nhds hx'.1 hx'.2] with y hy
    exact integral_zero_to_eq_mul hf hsym hy
  apply (hprimitive.congr_of_eventuallyEq heq.symm).unique
  simpa only [id_eq, one_mul] using
    (hasDerivAt_id x).mul_const (∫ t in (0 : ℝ)..1, f t)

end

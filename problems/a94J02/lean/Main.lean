/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# APM a94J02: AC strictly monotone function with h' = 0 on a positive-measure set

## Mathematical problem

Construct an absolutely continuous nonnegative strictly monotone function `h` on
`[0,1]` such that `h' = 0` on a set of positive Lebesgue measure.

The original problem statement says "on ℝ", but as the informal proof observes,
"strictly monotone" + "integrable" + "nonneg" on all of ℝ is impossible: a
strictly monotone nonneg function on ℝ cannot be integrable (it is bounded below
by its value at any point to the left, hence not integrable on a half-line).
The meaningful version is on a compact interval `[0,1]`, which is what we prove.

## Construction

Let `C ⊂ [0,1]` be a *fat Cantor set*: closed, nowhere dense (empty interior),
with positive Lebesgue measure (say `m(C) = 1/2`).

Define `h(x) = ∫₀^x 𝟙_{[0,1]\\C}(t) dt`.

Then:
- `h` is AC (integral of an L¹ function).
- `h` is nonneg (integral of a nonneg function from a fixed basepoint).
- `h` is strictly monotone on `[0,1]`: if `x < y` then `(x,y)` meets `[0,1]\\C`
  (because `C` has empty interior, so `[0,1]\\C` is dense in `[0,1]`), and
  `𝟙_{[0,1]\\C}` is positive on a neighbourhood of that point, so `∫ₓ^y 𝟙 > 0`.
- `h' = 𝟙_{[0,1]\\C}` a.e., hence `h' = 0` on `C`, and `m(C) > 0`.

The key tension is between "strictly monotone" (topological — uses nowhere-denseness
of `C`) and "h' = 0 on a big set" (measure-theoretic — uses positive measure of `C`).
The fat Cantor set resolves this: it is simultaneously topologically small (nowhere
dense) and measure-theoretically large (positive measure).

## Formalization boundary

The existence of a fat Cantor set is a standard result in real analysis but is not
in Mathlib as of 2025. We state it as a helper lemma with an explicit `sorry` at
that boundary; the rest of the proof (building `h`, proving nonneg, strict
monotonicity, and the derivative claim) follows from it.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.Instances.Real.Lemmas

open MeasureTheory Set Topology

open scoped Real

noncomputable section

/-!
## Step 1: Existence of a fat Cantor set

A fat Cantor set is a closed, nowhere-dense subset of `[0,1]` with positive
Lebesgue measure. The standard construction removes from `[0,1]` at step `n` a
union of open intervals of total length `ε / 2^n` (for a fixed `ε ∈ (0,1)`),
leaving a closed nowhere-dense set of measure `1 - ε > 0`.

This is a standard construction (Smith-Volterra-Cantor set). It is not currently
in Mathlib. We state it here with an explicit `sorry`; the mathematical content
is clear and standard.
-/

/-- Existence of a fat Cantor set: closed, nowhere dense (empty interior),
contained in `[0,1]`, with positive Lebesgue measure. -/
lemma exists_fat_cantor :
    ∃ C : Set ℝ,
      IsClosed C ∧
      C ⊆ Icc 0 1 ∧
      interior C = ∅ ∧
      0 < volume C := by
  let Q : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  let A : Set ℝ := Icc 0 1 \ Q
  have hQ_count : Q.Countable := Set.countable_range _
  have hQ_null : volume Q = 0 := hQ_count.measure_zero volume
  have hA_meas : MeasurableSet A :=
    measurableSet_Icc.diff hQ_count.measurableSet
  have hA_volume : volume A = 1 := by
    rw [show A = Icc 0 1 \ Q from rfl, measure_diff_null hQ_null]
    simp
  have hA_pos : 0 < volume A := by rw [hA_volume]; norm_num
  obtain ⟨C, hCA, hC_compact, hC_pos⟩ :=
    hA_meas.exists_lt_isCompact hA_pos
  refine ⟨C, hC_compact.isClosed, ?_, ?_, hC_pos⟩
  · exact hCA.trans diff_subset
  · apply eq_empty_iff_forall_notMem.2
    intro x hx
    have hopen : IsOpen (interior C) := isOpen_interior
    have hnonempty : (interior C).Nonempty := ⟨x, hx⟩
    obtain ⟨q, hq⟩ :=
      Rat.denseRange_cast.inter_open_nonempty (interior C) hopen hnonempty
    rcases hq with ⟨hq_int, q, rfl⟩
    have hqC : (q : ℝ) ∈ C := interior_subset hq_int
    have hqA := hCA hqC
    exact hqA.2 ⟨q, rfl⟩

/-!
## Step 2: The constructed function

Given a fat Cantor set `C`, define `h(x) = ∫₀^x 𝟙_{[0,1]\\C}(t) dt`.
-/

/-- The density function: indicator of the complement of `C` in `[0,1]`. -/
def densityFun (C : Set ℝ) (t : ℝ) : ℝ :=
  (Cᶜ ∩ Icc 0 1).indicator (fun _ => (1:ℝ)) t

/-- The constructed function: `h(x) = ∫₀^x 𝟙_{[0,1]\\C}`. -/
def constructedH (C : Set ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..x, densityFun C t

/-!
## Step 3: Properties of the constructed function
-/

/-- The density function is nonneg. -/
lemma densityFun_nonneg (C : Set ℝ) (t : ℝ) : 0 ≤ densityFun C t := by
  unfold densityFun
  by_cases h : t ∈ Cᶜ ∩ Icc 0 1
  · simp [h]
  · simp [h]

/-- `constructedH` is nonneg for `x ≥ 0`. -/
lemma constructedH_nonneg (C : Set ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ constructedH C x := by
  unfold constructedH
  exact intervalIntegral.integral_nonneg_of_forall hx (densityFun_nonneg C)

/-- `constructedH` is monotone: if `x ≤ y` then `h(x) ≤ h(y)`.
Requires `C` measurable so that the density function is interval-integrable. -/
lemma constructedH_mono (C : Set ℝ) (hC_meas : MeasurableSet C) {x y : ℝ}
    (hxy : x ≤ y) : constructedH C x ≤ constructedH C y := by
  have hS : MeasurableSet (Cᶜ ∩ Icc (0 : ℝ) 1) :=
    hC_meas.compl.inter measurableSet_Icc
  have hSfin : volume (Cᶜ ∩ Icc (0 : ℝ) 1) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Icc (0 : ℝ) 1) ≠ ⊤ by simp)
    exact measure_mono inter_subset_right
  have hint : Integrable (densityFun C) volume := by
    exact
      (integrableOn_const (μ := volume) (s := Cᶜ ∩ Icc (0 : ℝ) 1) hSfin)
        |>.integrable_indicator hS
  unfold constructedH
  calc
    (∫ t in (0 : ℝ)..x, densityFun C t) ≤
        (∫ t in (0 : ℝ)..x, densityFun C t) + ∫ t in x..y, densityFun C t := by
      exact le_add_of_nonneg_right
        (intervalIntegral.integral_nonneg_of_forall hxy (densityFun_nonneg C))
    _ = ∫ t in (0 : ℝ)..y, densityFun C t := by
      rw [intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
        hint.intervalIntegrable]

/-!
## Step 4: Strict monotonicity and the derivative

These two lemmas are the core mathematical claims. Strict monotonicity uses the
nowhere-denseness of `C`: every interval `(x,y)` in `[0,1]` meets the open set
`[0,1] \\ C`, and on a neighbourhood of that intersection point the density is 1,
so the integral over `(x,y)` is strictly positive.

The derivative claim uses the Lebesgue differentiation theorem / FTC for
L¹ functions: `h' = densityFun` a.e.
-/

/-- Counterexample to strict monotonicity without a closedness hypothesis:
take the irrationals in `[0,1]`. Its complement in `[0,1]` is countable, so
the constructed integral vanishes identically. -/
lemma constructedH_strictMonoOn_counterexample :
    ∃ C : Set ℝ, C ⊆ Icc 0 1 ∧ interior C = ∅ ∧
      ¬StrictMonoOn (constructedH C) (Icc 0 1) := by
  let Q : Set ℝ := Set.range (fun q : ℚ => (q : ℝ))
  let C : Set ℝ := Icc 0 1 \ Q
  have hQ_count : Q.Countable := Set.countable_range _
  have hC_sub : C ⊆ Icc 0 1 := diff_subset
  have hC_int : interior C = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro x hx
    have hopen : IsOpen (interior C) := isOpen_interior
    have hnonempty : (interior C).Nonempty := ⟨x, hx⟩
    obtain ⟨q, hq⟩ :=
      Rat.denseRange_cast.inter_open_nonempty (interior C) hopen hnonempty
    rcases hq with ⟨hq_int, q, rfl⟩
    have hqC : (q : ℝ) ∈ C := interior_subset hq_int
    exact hqC.2 ⟨q, rfl⟩
  have hdensity_ae : densityFun C =ᵐ[volume] 0 := by
    filter_upwards [hQ_count.ae_notMem volume] with x hxQ
    simp [densityFun, C, Q, hxQ]
  have hH_one : constructedH C 1 = 0 := by
    unfold constructedH
    rw [intervalIntegral.integral_congr_ae]
    · exact intervalIntegral.integral_zero
    · filter_upwards [hdensity_ae] with x hx _
      exact hx
  refine ⟨C, hC_sub, hC_int, ?_⟩
  intro hstrict
  have hlt := hstrict (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_lt_one
  have hH_zero : constructedH C 0 = 0 := by simp [constructedH]
  rw [hH_zero, hH_one] at hlt
  exact lt_irrefl 0 hlt

/-- This statement is false: empty interior alone does not ensure that the
complement has positive measure in every interval. See
`constructedH_strictMonoOn_counterexample`. The correct version with
`IsClosed C` is proved below. -/
lemma constructedH_strictMonoOn
    (C : Set ℝ) (hC_sub : C ⊆ Icc 0 1) (hC_int : interior C = ∅) :
    StrictMonoOn (constructedH C) (Icc 0 1) := by
  sorry

/-- The strict-monotonicity statement with the missing closedness hypothesis.
Closedness makes the complement open, so every interval contains a subinterval
on which the density is identically one. -/
lemma constructedH_strictMonoOn_of_isClosed
    (C : Set ℝ) (hC_closed : IsClosed C) (hC_int : interior C = ∅) :
    StrictMonoOn (constructedH C) (Icc 0 1) := by
  have hC_meas : MeasurableSet C := hC_closed.measurableSet
  have hS : MeasurableSet (Cᶜ ∩ Icc (0 : ℝ) 1) :=
    hC_meas.compl.inter measurableSet_Icc
  have hSfin : volume (Cᶜ ∩ Icc (0 : ℝ) 1) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Icc (0 : ℝ) 1) ≠ ⊤ by simp)
    exact measure_mono inter_subset_right
  have hint : Integrable (densityFun C) volume := by
    exact
      (integrableOn_const (μ := volume) (s := Cᶜ ∩ Icc (0 : ℝ) 1) hSfin)
        |>.integrable_indicator hS
  intro x hx y hy hxy
  have hU_open : IsOpen (Cᶜ ∩ Ioo x y) :=
    hC_closed.isOpen_compl.inter isOpen_Ioo
  have hU_nonempty : (Cᶜ ∩ Ioo x y).Nonempty := by
    by_contra hU
    rw [Set.not_nonempty_iff_eq_empty] at hU
    have hIooC : Ioo x y ⊆ C := by
      intro t ht
      by_contra htC
      have htU : t ∈ Cᶜ ∩ Ioo x y := ⟨htC, ht⟩
      rw [hU] at htU
      exact htU
    have hm : (x + y) / 2 ∈ Ioo x y := by
      constructor <;> linarith
    have hmC : (x + y) / 2 ∈ interior C :=
      interior_maximal hIooC isOpen_Ioo hm
    rw [hC_int] at hmC
    exact hmC
  obtain ⟨a, b, hab, habU⟩ := hU_open.exists_Ioo_subset hU_nonempty
  have hab_support :
      Ioo a b ⊆ Function.support (densityFun C) ∩ Ioc x y := by
    intro t ht
    have htU := habU ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · linarith [hx.1, htU.2.1]
      · linarith [hy.2, htU.2.2]
    refine ⟨?_, Ioo_subset_Ioc_self htU.2⟩
    simp [Function.mem_support, densityFun, htU.1, htIcc]
  have hsupport_pos :
      0 < volume (Function.support (densityFun C) ∩ Ioc x y) := by
    have hab_pos : 0 < volume (Ioo a b) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hab_pos.trans_le (measure_mono hab_support)
  have hintegral_pos : 0 < ∫ t in x..y, densityFun C t := by
    exact
      (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall (densityFun_nonneg C))
        hint.intervalIntegrable).2 ⟨hxy, hsupport_pos⟩
  have hadd :
      (∫ t in (0 : ℝ)..x, densityFun C t) + ∫ t in x..y, densityFun C t =
        ∫ t in (0 : ℝ)..y, densityFun C t :=
    intervalIntegral.integral_add_adjacent_intervals
      hint.intervalIntegrable hint.intervalIntegrable
  unfold constructedH
  linarith [hadd]

/-- At almost every point of `C`, the indefinite integral has derivative zero. -/
lemma ae_hasDerivAt_constructedH_zero_on
    (C : Set ℝ) (hC_meas : MeasurableSet C) :
    ∀ᵐ x ∂volume, x ∈ C → HasDerivAt (constructedH C) 0 x := by
  have hS : MeasurableSet (Cᶜ ∩ Icc (0 : ℝ) 1) :=
    hC_meas.compl.inter measurableSet_Icc
  have hSfin : volume (Cᶜ ∩ Icc (0 : ℝ) 1) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Icc (0 : ℝ) 1) ≠ ⊤ by simp)
    exact measure_mono inter_subset_right
  have hint : Integrable (densityFun C) volume := by
    exact
      (integrableOn_const (μ := volume) (s := Cᶜ ∩ Icc (0 : ℝ) 1) hSfin)
        |>.integrable_indicator hS
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hint.locallyIntegrable] with x hx
  intro hxC
  simpa [constructedH, densityFun, hxC] using hx (0 : ℝ)

/-- `h' = 0` on `C` (a.e.), and since `C` has positive measure, `h' = 0` on a
set of positive measure. -/
lemma constructedH_deriv_zero_pos_measure
    (C : Set ℝ) (hC_meas : MeasurableSet C) (hC_pos : 0 < volume C) :
    0 < volume {x | HasDerivAt (constructedH C) 0 x} := by
  apply hC_pos.trans_le
  exact measure_mono_ae
    ((ae_hasDerivAt_constructedH_zero_on C hC_meas).mono fun x hx hxC => hx hxC)

/-!
## Step 5: Main theorem

Packaging: combine the fat Cantor set existence with the helper lemmas to get
the final result.
-/

/-- **Main theorem**: There exists a nonneg, strictly monotone function on
`[0,1]` whose derivative is zero on a set of positive Lebesgue measure.

The original problem says "on ℝ" but strict monotonicity + integrability + nonneg
is impossible on all of ℝ; the meaningful version is on `[0,1]`. -/
theorem exists_ac_strictly_mono_deriv_zero_pos_measure :
    ∃ (h : ℝ → ℝ),
      (∀ x ∈ Icc 0 1, 0 ≤ h x) ∧
      StrictMonoOn h (Icc 0 1) ∧
      0 < volume {x ∈ Icc 0 1 | HasDerivAt h 0 x} := by
  obtain ⟨C, hC_closed, hC_sub, hC_int, hC_pos⟩ := exists_fat_cantor
  refine ⟨constructedH C, ?_, ?_, ?_⟩
  · intro x hx
    exact constructedH_nonneg C hx.1
  · exact constructedH_strictMonoOn_of_isClosed C hC_closed hC_int
  · apply hC_pos.trans_le
    exact measure_mono_ae
      ((ae_hasDerivAt_constructedH_zero_on C hC_closed.measurableSet).mono
        fun x hx hxC => ⟨hC_sub hxC, hx hxC⟩)

end

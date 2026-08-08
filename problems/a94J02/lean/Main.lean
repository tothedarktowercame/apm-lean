import Mathlib

/-!
# APM a94J02 — an absolutely continuous strictly increasing function

## Statement repairs

The domain is changed from all of `ℝ` to `[0,1]`. The literal source is
inconsistent: a nonnegative strictly monotone function on `ℝ` cannot be
Lebesgue integrable, since one of its half-lines has a positive constant lower
bound. The compact-interval version is the standard intended problem.

Absolute continuity and integrability are stated explicitly, rather than only
suggested by the construction.
-/

open MeasureTheory Set

noncomputable section

/-- A compact positive-measure subset of `[0,1]` with empty interior.  This
fat-set construction is reused from the later problem-specific development at
commit `37f2405`: remove the countable dense set of rational points and apply
inner regularity. -/
lemma apm_a94J02_exists_fat_compact :
    ∃ C : Set ℝ,
      IsClosed C ∧ C ⊆ Icc 0 1 ∧ interior C = ∅ ∧ 0 < volume C := by
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
  refine ⟨C, hC_compact.isClosed, hCA.trans diff_subset, ?_, hC_pos⟩
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨q, hq_int, hqQ⟩ :=
    Rat.denseRange_cast.inter_open_nonempty (interior C) isOpen_interior ⟨x, hx⟩
  rcases hqQ with ⟨r, rfl⟩
  have hqC : (r : ℝ) ∈ C := interior_subset hq_int
  exact (hCA hqC).2 ⟨r, rfl⟩

def apm_a94J02_density (C : Set ℝ) (t : ℝ) : ℝ :=
  (Cᶜ ∩ Icc 0 1).indicator (fun _ ↦ 1) t

def apm_a94J02_H (C : Set ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, apm_a94J02_density C t

lemma apm_a94J02_density_nonneg (C : Set ℝ) (t : ℝ) :
    0 ≤ apm_a94J02_density C t := by
  simp only [apm_a94J02_density, Set.indicator]
  split <;> norm_num

lemma apm_a94J02_density_norm_le_one (C : Set ℝ) (t : ℝ) :
    ‖apm_a94J02_density C t‖ ≤ 1 := by
  simp only [apm_a94J02_density, Set.indicator]
  split <;> norm_num

lemma apm_a94J02_density_integrable (C : Set ℝ) (hC : MeasurableSet C) :
    Integrable (apm_a94J02_density C) volume := by
  have hS : MeasurableSet (Cᶜ ∩ Icc (0 : ℝ) 1) := hC.compl.inter measurableSet_Icc
  have hfin : volume (Cᶜ ∩ Icc (0 : ℝ) 1) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume (Icc (0 : ℝ) 1) ≠ ⊤ by simp)
    exact measure_mono inter_subset_right
  exact ((integrableOn_const (s := Cᶜ ∩ Icc (0 : ℝ) 1) hfin).integrable_indicator hS)

lemma apm_a94J02_H_nonneg (C : Set ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ apm_a94J02_H C x := by
  exact intervalIntegral.integral_nonneg_of_forall hx (apm_a94J02_density_nonneg C)

lemma apm_a94J02_H_sub (C : Set ℝ) (hC : MeasurableSet C) (x y : ℝ) :
    apm_a94J02_H C y - apm_a94J02_H C x =
      ∫ t in x..y, apm_a94J02_density C t := by
  rw [apm_a94J02_H, apm_a94J02_H,
    ← intervalIntegral.integral_add_adjacent_intervals
      (apm_a94J02_density_integrable C hC).intervalIntegrable
      (apm_a94J02_density_integrable C hC).intervalIntegrable]
  ring

lemma apm_a94J02_H_lipschitz (C : Set ℝ) (hC : MeasurableSet C) :
    LipschitzOnWith 1 (apm_a94J02_H C) (Icc (0 : ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x _ y _
  rw [dist_eq_norm, ← neg_sub, norm_neg, apm_a94J02_H_sub C hC]
  simpa [Real.dist_eq, abs_sub_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ ↦ apm_a94J02_density_norm_le_one C t)

lemma apm_a94J02_H_strictMonoOn (C : Set ℝ) (hC : IsClosed C)
    (hCint : interior C = ∅) : StrictMonoOn (apm_a94J02_H C) (Icc 0 1) := by
  have hCm := hC.measurableSet
  intro x hx y hy hxy
  have hUopen : IsOpen (Cᶜ ∩ Ioo x y) := hC.isOpen_compl.inter isOpen_Ioo
  have hUne : (Cᶜ ∩ Ioo x y).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have hsub : Ioo x y ⊆ C := by
      intro t ht
      by_contra htC
      have : t ∈ Cᶜ ∩ Ioo x y := ⟨htC, ht⟩
      simpa [h] using this
    have hm : (x + y) / 2 ∈ Ioo x y := by constructor <;> linarith
    have := interior_maximal hsub isOpen_Ioo hm
    simpa [hCint] using this
  obtain ⟨a, b, hab, habU⟩ := hUopen.exists_Ioo_subset hUne
  have hsupp : Ioo a b ⊆ Function.support (apm_a94J02_density C) ∩ Ioc x y := by
    intro t ht
    have hu := habU ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1, hu.2.1], by linarith [hy.2, hu.2.2]⟩
    refine ⟨?_, Ioo_subset_Ioc_self hu.2⟩
    simp [Function.mem_support, apm_a94J02_density, hu.1, ht01]
  have hsupppos : 0 < volume (Function.support (apm_a94J02_density C) ∩ Ioc x y) := by
    apply (show 0 < volume (Ioo a b) by simp [Real.volume_Ioo, ENNReal.ofReal_pos, hab]).trans_le
    exact measure_mono hsupp
  have hpos : 0 < ∫ t in x..y, apm_a94J02_density C t :=
    (intervalIntegral.integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall (apm_a94J02_density_nonneg C))
      (apm_a94J02_density_integrable C hCm).intervalIntegrable).2 ⟨hxy, hsupppos⟩
  rw [← apm_a94J02_H_sub C hCm] at hpos
  linarith

lemma apm_a94J02_ae_deriv_zero_on (C : Set ℝ) (hC : MeasurableSet C) :
    ∀ᵐ x ∂volume, x ∈ C → HasDerivAt (apm_a94J02_H C) 0 x := by
  have hi := apm_a94J02_density_integrable C hC
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hi.locallyIntegrable] with x hx
  intro hxC
  simpa [apm_a94J02_H, apm_a94J02_density, hxC] using hx (0 : ℝ)

theorem apm_a94j02 :
    ∃ h : ℝ → ℝ,
      AbsolutelyContinuousOnInterval h 0 1 ∧
      IntervalIntegrable h volume 0 1 ∧
      (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ h x) ∧
      StrictMonoOn h (Icc (0 : ℝ) 1) ∧
      0 < volume {x ∈ Icc (0 : ℝ) 1 | HasDerivAt h 0 x} := by
  /-
  CLOSER HOP 1: git history contains a later a94J02 development, but its final
  theorem omits the frozen statement's `AbsolutelyContinuousOnInterval` and
  `IntervalIntegrable` conjuncts, so it cannot close this target verbatim.
  Its sound fat-set construction has been extracted above as the compiled,
  sorry-free lemma `apm_a94J02_exists_fat_compact`.

  CLOSER HOP 2: the historical strict-monotonicity and derivative arguments
  are now ported above. The indefinite integral is proved `1`-Lipschitz from
  the pointwise density bound, which supplies absolute continuity; continuity
  then supplies interval integrability. The a.e. FTC and the positive-measure
  compact set close the derivative-zero clause. No statement defect was found.
  -/
  obtain ⟨C, hCclosed, hCsub, hCint, hCpos⟩ := apm_a94J02_exists_fat_compact
  have hCm : MeasurableSet C := hCclosed.measurableSet
  let h := apm_a94J02_H C
  have hlip : LipschitzOnWith 1 h (uIcc (0 : ℝ) 1) := by
    simpa [h, uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      apm_a94J02_H_lipschitz C hCm
  have hac : AbsolutelyContinuousOnInterval h 0 1 :=
    hlip.absolutelyContinuousOnInterval
  refine ⟨h, hac, hac.continuousOn.intervalIntegrable, ?_, ?_, ?_⟩
  · intro x hx
    exact apm_a94J02_H_nonneg C hx.1
  · exact apm_a94J02_H_strictMonoOn C hCclosed hCint
  · apply hCpos.trans_le
    exact measure_mono_ae
      ((apm_a94J02_ae_deriv_zero_on C hCm).mono fun x hx hxC ↦
        ⟨hCsub hxC, hx hxC⟩)

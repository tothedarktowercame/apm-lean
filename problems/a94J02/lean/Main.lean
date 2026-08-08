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

  The historical development also proves strict monotonicity and the positive-
  measure derivative-zero claim for the indefinite integral of the indicator
  of `Cᶜ ∩ Icc 0 1`.  Finishing this frozen theorem requires porting those
  integral helpers and additionally packaging Mathlib's indefinite-integral
  absolute-continuity theorem plus interval integrability of the resulting
  bounded monotone function. No statement defect was found.
  -/
  sorry

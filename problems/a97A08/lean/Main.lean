import Mathlib

open Complex Polynomial Set Metric

noncomputable section

/-- The polynomial f(z) = z⁵ + 15z + 1. -/
def apm_a97A08_f : Polynomial ℂ :=
  Polynomial.X ^ 5 + 15 * Polynomial.X + 1

/-- Helper: |15z + 1| < |z⁵| on the circle |z| = 2. -/
theorem apm_a97A08_rouche_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    ‖15 * z + 1‖ < ‖z ^ 5‖ := by
  have h1 : ‖15 * z + 1‖ ≤ 31 := by
    calc
      ‖15 * z + 1‖ ≤ ‖15 * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 15 * ‖z‖ + 1 := by simp
      _ = 31 := by rw [hz]; norm_num
  have h2 : ‖z ^ 5‖ = 32 := by
    rw [norm_pow, hz]
    norm_num
  exact lt_of_le_of_lt h1 (by simpa [h2] using (show (31 : ℝ) < 32 by norm_num))

/-- Helper: |z⁵ + 1| < |15z| on the circle |z| = 3/2. -/
theorem apm_a97A08_rouche_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    ‖z ^ 5 + 1‖ < ‖15 * z‖ := by
  have h1 : ‖z ^ 5 + 1‖ ≤ (3 / 2 : ℝ) ^ 5 + 1 := by
    calc
      ‖z ^ 5 + 1‖ ≤ ‖z ^ 5‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ ^ 5 + 1 := by simp [norm_pow]
      _ = (3 / 2 : ℝ) ^ 5 + 1 := by rw [hz]
  have h2 : ‖15 * z‖ = 15 * (3 / 2 : ℝ) := by
    rw [norm_mul, hz]
    norm_num
  have hlt : ((3 / 2 : ℝ) ^ 5 + 1) < 15 * (3 / 2 : ℝ) := by
    norm_num
  rw [h2]
  exact lt_of_le_of_lt h1 hlt

/-- f has no zeros on |z| = 2 (so the count on the open disk is well-defined). -/
theorem apm_a97A08_no_zeros_outer
    (z : ℂ) (hz : ‖z‖ = 2) :
    apm_a97A08_f.aeval z ≠ 0 := by
  intro hzero
  have hzero' : z ^ 5 + 15 * z + 1 = 0 := by
    simpa [apm_a97A08_f, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hzero
  have hnorm : ‖15 * z + 1‖ = ‖z ^ 5‖ := by
    have hz5 : z ^ 5 = -(15 * z + 1) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc, add_comm, add_left_comm] using hzero'
    rw [hz5, norm_neg]
  nlinarith [apm_a97A08_rouche_outer z hz, hnorm]

/-- f has no zeros on |z| = 3/2. -/
theorem apm_a97A08_no_zeros_inner
    (z : ℂ) (hz : ‖z‖ = 3/2) :
    apm_a97A08_f.aeval z ≠ 0 := by
  intro hzero
  have hzero' : z ^ 5 + 15 * z + 1 = 0 := by
    simpa [apm_a97A08_f, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hzero
  have hnorm : ‖z ^ 5 + 1‖ = ‖15 * z‖ := by
    have hz5 : z ^ 5 + 1 = -(15 * z) := by
      apply eq_neg_of_add_eq_zero_left
      simpa [add_assoc, add_comm, add_left_comm] using hzero'
    rw [hz5, norm_neg]
  nlinarith [apm_a97A08_rouche_inner z hz, hnorm]

/-- f has 5 zeros (with multiplicity) in the open disk |z| < 2. -/
theorem apm_a97A08_count_outer :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 := by
  have hdeg : apm_a97A08_f.natDegree = 5 := by
    rw [show apm_a97A08_f =
        Polynomial.X ^ 5 + (15 * Polynomial.X + 1) by
      simp only [apm_a97A08_f]
      ring]
    have hq :
        (15 * Polynomial.X + 1 : Polynomial ℂ).natDegree <
          (Polynomial.X ^ 5 : Polynomial ℂ).natDegree := by
      rw [Polynomial.natDegree_X_pow]
      calc
        (15 * Polynomial.X + 1 : Polynomial ℂ).natDegree
            ≤ max (15 * Polynomial.X : Polynomial ℂ).natDegree
                (1 : Polynomial ℂ).natDegree :=
          Polynomial.natDegree_add_le _ _
        _ ≤ 1 := by norm_num
        _ < 5 := by norm_num
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hq,
      Polynomial.natDegree_X_pow]
  have hall : ∀ z ∈ apm_a97A08_f.roots, ‖z‖ < 2 := by
    intro z hz
    have hzero : z ^ 5 + 15 * z + 1 = 0 := by
      have := Polynomial.isRoot_of_mem_roots hz
      simpa [Polynomial.IsRoot, apm_a97A08_f, add_assoc, add_comm,
        add_left_comm, mul_assoc, mul_comm, mul_left_comm] using this
    have hnorm : ‖z‖ ^ 5 ≤ 15 * ‖z‖ + 1 := by
      have hz5 : z ^ 5 = -(15 * z + 1) := by
        apply eq_neg_of_add_eq_zero_left
        simpa [add_assoc, add_comm, add_left_comm] using hzero
      rw [← norm_pow, hz5, norm_neg]
      calc
        ‖15 * z + 1‖ ≤ ‖15 * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = 15 * ‖z‖ + 1 := by simp
    by_contra hnot
    have hr : 2 ≤ ‖z‖ := le_of_not_gt hnot
    have hr0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hr_sq : (4 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
    have hr_four : (16 : ℝ) ≤ ‖z‖ ^ 4 := by nlinarith [sq_nonneg (‖z‖ ^ 2 - 4)]
    have hmul : 16 * ‖z‖ ≤ ‖z‖ ^ 5 := by
      calc
        16 * ‖z‖ ≤ ‖z‖ ^ 4 * ‖z‖ :=
          mul_le_mul_of_nonneg_right hr_four hr0
        _ = ‖z‖ ^ 5 := by ring
    nlinarith
  rw [Multiset.filter_eq_self.2 hall]
  have hsplits : apm_a97A08_f.Splits :=
    IsAlgClosed.splits apm_a97A08_f
  rw [← hsplits.natDegree_eq_card_roots, hdeg]

/-- f has 1 zero in the open disk |z| < 3/2. -/
theorem apm_a97A08_count_inner :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3/2)).card = 1 := by
  /-
  Remaining construction: apply Rouché on `‖z‖ = 3/2`, with dominant
  polynomial `15 * X` and perturbation `X^5 + 1`, using
  `apm_a97A08_rouche_inner`.  `ConstructionTargets.Rouche` packages the
  boundary-nonvanishing homotopy, but its divisor-count invariance theorem
  `zeroCountInClosedBall_add_eq` still contains `sorry`.
  -/
  sorry

/-- Main theorem: the count in disk |z| < 2 is 5, and the count in
    annulus 3/2 < |z| < 2 is 4. -/
theorem apm_a97A08_main :
    (apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)).card = 5 ∧
    (apm_a97A08_f.roots.filter (fun z => 3/2 < ‖z‖ ∧ ‖z‖ < 2)).card = 4 := by
  refine ⟨apm_a97A08_count_outer, ?_⟩
  let s := apm_a97A08_f.roots.filter (fun z => ‖z‖ < 2)
  have hpartition :=
    Multiset.filter_add_not (p := fun z : ℂ => ‖z‖ < 3 / 2) s
  have hinner :
      s.filter (fun z => ‖z‖ < 3 / 2) =
        apm_a97A08_f.roots.filter (fun z => ‖z‖ < 3 / 2) := by
    simp only [s, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z hz
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, h.trans (by norm_num)⟩
  have hannulus :
      s.filter (fun z => ¬ ‖z‖ < 3 / 2) =
        apm_a97A08_f.roots.filter (fun z => 3 / 2 < ‖z‖ ∧ ‖z‖ < 2) := by
    simp only [s, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro z hz
    have hboundary : ‖z‖ ≠ 3 / 2 := by
      intro heq
      apply apm_a97A08_no_zeros_inner z heq
      have hzroot := Polynomial.isRoot_of_mem_roots hz
      simpa [Polynomial.IsRoot, Polynomial.aeval_def,
        Polynomial.coe_aeval_eq_eval] using hzroot
    constructor
    · rintro ⟨hge, hout⟩
      exact ⟨lt_of_le_of_ne (le_of_not_gt hge) hboundary.symm, hout⟩
    · rintro ⟨hin, hout⟩
      exact ⟨not_lt_of_ge hin.le, hout⟩
  have hcard := congrArg Multiset.card hpartition
  rw [Multiset.card_add, hinner, hannulus, apm_a97A08_count_inner,
    show s.card = 5 by simpa [s] using apm_a97A08_count_outer] at hcard
  omega

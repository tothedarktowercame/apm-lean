import Mathlib

open MeasureTheory Set Filter Topology

noncomputable section

/-- The n-th Rademacher function on [0,1]: +1 on odd dyadic intervals,
    -1 on even dyadic intervals. -/
def rademacher (n : ℕ) (t : ℝ) : ℝ :=
  if t = 1 then -1
  else
    let k := ⌊t * 2^n⌋₊ + 1
    if k % 2 = 1 then 1 else -1

/-- The Rademacher function integrates to 0 over any dyadic interval at
    a strictly coarser level. -/
theorem apm_a97A01_int_dyadic_zero
    (m n : ℕ) (hmn : m < n) (j : ℕ) (hj : j < 2 ^ m) :
    ∫ t in Set.Ico (j / (2:ℝ)^m) ((j+1) / (2:ℝ)^m), rademacher n t = 0 := by sorry

/-- The Rademacher function is essentially bounded by 1. -/
theorem apm_a97A01_rademacher_bound (n : ℕ) (t : ℝ) :
    |rademacher n t| ≤ 1 := by
  unfold rademacher
  by_cases h1 : t = 1
  · simp [h1]
  · simp [h1]
    by_cases h2 : (⌊t * 2 ^ n⌋₊ + 1) % 2 = 1 <;> simp [h2]

/-- The Rademacher function is measurable. -/
theorem apm_a97A01_rademacher_measurable (n : ℕ) :
    Measurable (rademacher n) := by
  classical
  unfold rademacher
  refine Measurable.piecewise ?_ measurable_const ?_
  · exact measurableSet_singleton 1
  · refine Measurable.piecewise ?_ measurable_const measurable_const
    have h1 : Measurable fun t : ℝ => t * (2 ^ n : ℝ) := measurable_id.mul_const (2 ^ n : ℝ)
    have h2 : Measurable fun t : ℝ => (⌊t * (2 ^ n : ℝ)⌋₊ : ℕ) := Measurable.nat_floor h1
    have h3 : Measurable fun t : ℝ => (((⌊t * (2 ^ n : ℝ)⌋₊ : ℕ) + 1) % 2 : ℕ) :=
      (measurable_of_countable fun k : ℕ => k % 2).comp (h2.add_const 1)
    exact measurableSet_preimage h3 (measurableSet_singleton 1)

/-- Dyadic step functions are dense in L¹([0,1]). -/
theorem apm_a97A01_dyadic_dense_L1
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc 0 1) volume) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (s : ℝ → ℝ),
      (∀ t, t ∈ Set.Icc (0:ℝ) 1 → ∃ j : ℕ, j < 2^m ∧
        s t = s (j / (2:ℝ)^m)) ∧
      ∫ t in Set.Icc (0:ℝ) 1, |f t - s t| < ε := by sorry

/-- Main theorem: ∫ f · f_n → 0 for f ∈ L^∞([0,1]) and f_n the Rademacher functions. -/
theorem apm_a97A01_main
    (f : ℝ → ℝ) (hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Icc 0 1)))
    (M : ℝ) (hf_bdd : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 1)), |f t| ≤ M) :
    Tendsto (fun n : ℕ => ∫ t in Set.Icc (0:ℝ) 1, f t * rademacher n t)
      atTop (nhds 0) := by sorry

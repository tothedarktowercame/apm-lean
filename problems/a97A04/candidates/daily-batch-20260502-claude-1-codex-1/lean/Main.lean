import Mathlib

open MeasureTheory Filter Set

variable {X : Type*} [MeasurableSpace X]

/-- The set where a sequence of measurable functions converges is measurable.
    Bounded hypothesis is not strictly needed in ℝ but matches the problem. -/
theorem apm_a97A04_main
    (f : ℕ → X → ℝ)
    (hf : ∀ n, Measurable (f n))
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    MeasurableSet {x : X | ∃ L : ℝ, Filter.Tendsto (fun n => f n x) atTop (nhds L)} := by
  have hEq :
      {x : X | ∃ L : ℝ, Filter.Tendsto (fun n => f n x) atTop (nhds L)} =
      ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ m : ℕ,
        {x : X | n ≥ N → m ≥ N → |f n x - f m x| < 1 / (k + 1 : ℝ)} := by
    ext x
    constructor
    · intro hx
      simp only [mem_setOf_eq, mem_iInter, mem_iUnion]
      intro k
      have hc : CauchySeq (fun n => f n x) := hx.choose_spec.cauchySeq
      have hk : 0 < 1 / (k + 1 : ℝ) := by positivity
      obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hc) (1 / (k + 1 : ℝ)) hk
      refine ⟨N, ?_⟩
      intro n
      intro m
      intro hn hm
      simpa [Real.dist_eq] using hN n hn m hm
    · intro hx
      simp only [mem_setOf_eq, mem_iInter, mem_iUnion] at hx
      have hc : CauchySeq (fun n => f n x) := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        rcases hx k with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro n hn m hm
        have hnm := hN n m hn hm
        have : |f n x - f m x| < ε := lt_of_lt_of_le hnm hk.le
        simpa [Real.dist_eq] using this
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
      exact ⟨L, hL⟩
  rw [hEq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro m
  by_cases hn : n ≥ N <;> by_cases hm : m ≥ N
  · simpa [hn, hm] using
      (measurableSet_lt ((hf n).sub (hf m)).norm measurable_const)
  · simp [hn, hm]
  · simp [hn, hm]
  · simp [hn, hm]

/-- Helper: the set where two measurable functions are within ε is measurable. -/
theorem apm_a97A04_close_set_measurable
    (g h : X → ℝ) (hg : Measurable g) (hh : Measurable h) (ε : ℝ) :
    MeasurableSet {x : X | |g x - h x| < ε} := by
  simpa using measurableSet_lt (hg.sub hh).norm measurable_const

/-- Helper: limsup of a sequence of measurable functions is measurable. -/
theorem apm_a97A04_limsup_measurable
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    Measurable (fun x => Filter.limsup (fun n => f n x) atTop) := by
  simpa using Measurable.limsup hf

/-- Helper: liminf of a sequence of measurable functions is measurable. -/
theorem apm_a97A04_liminf_measurable
    (f : ℕ → X → ℝ) (hf : ∀ n, Measurable (f n))
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    Measurable (fun x => Filter.liminf (fun n => f n x) atTop) := by
  simpa using Measurable.liminf hf

/-- Convergence set = Cauchy set (for bounded real sequences this is the same). -/
theorem apm_a97A04_conv_eq_cauchy
    (f : ℕ → X → ℝ)
    (hbdd : ∀ x : X, ∃ M : ℝ, ∀ n : ℕ, |f n x| ≤ M) :
    {x : X | ∃ L : ℝ, Filter.Tendsto (fun n => f n x) atTop (nhds L)} =
    ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ m : ℕ,
      {x : X | n ≥ N → m ≥ N → |f n x - f m x| < 1 / (k + 1 : ℝ)} := by
  ext x
  constructor
  · intro hx
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion]
    intro k
    have hc : CauchySeq (fun n => f n x) := hx.choose_spec.cauchySeq
    have hk : 0 < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hc) (1 / (k + 1 : ℝ)) hk
    refine ⟨N, ?_⟩
    intro n
    intro m
    intro hn hm
    simpa [Real.dist_eq] using hN n hn m hm
  · intro hx
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion] at hx
    have hc : CauchySeq (fun n => f n x) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      rcases hx k with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn m hm
      have hnm := hN n m hn hm
      have : |f n x - f m x| < ε := lt_of_lt_of_le hnm hk.le
      simpa [Real.dist_eq] using this
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨L, hL⟩

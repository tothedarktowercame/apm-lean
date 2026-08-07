import Mathlib

/-! # APM m03J03: examples and derivatives of distributions

## Statement repairs

None.  Mathlib's distribution convention uses real-valued test functions and
allows complex-valued distributions, which faithfully accommodates every part.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

noncomputable section

/-- The Heaviside function with the irrelevant value at zero chosen to be zero. -/
def m03J03Heaviside (x : ℝ) : ℝ := if 0 < x then 1 else 0

lemma m03J03_abs_eval_not_distribution :
    ¬ ∃ T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤, T φ = |φ 0| := by
  rintro ⟨T, hT⟩
  let b : ContDiffBump (0 : ℝ) := default
  let φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤ :=
    ⟨b, b.contDiff, b.hasCompactSupport, subset_univ _⟩
  have hφ : φ 0 = 1 := by
    exact b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hpos := hT φ
  have hneg := hT (-φ)
  rw [map_neg, hpos] at hneg
  simp [hφ] at hneg
  norm_num at hneg

/-- The one-sided Dirac comb, polynomial-growth Fourier series, the two
distributional derivatives of `H sin`, and the absolute-value non-example. -/
theorem apm_m03j03 :
    (∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∑' n : ℕ, (φ n : ℂ)) ∧
    (∀ a : ℕ → ℂ, (∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧
        ∀ n : ℕ, ‖a n‖ ≤ A * (n : ℝ) ^ N) →
      ∃ T : Distribution (⊤ : Opens ℝ) ℂ ⊤,
        ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
          HasSum (fun n : ℕ =>
            a n * (∫ x : ℝ,
              Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) * φ x)) (T φ)) ∧
    (∃ T DT D2T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        T φ = ∫ x : ℝ, m03J03Heaviside x * Real.sin x * φ x ∧
        DT φ = -∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * deriv φ x ∧
        DT φ = ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x ∧
        D2T φ = ∫ x : ℝ,
          m03J03Heaviside x * Real.sin x * iteratedDeriv 2 φ x ∧
        D2T φ = φ 0 - T φ) ∧
    (¬ ∃ T : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤, T φ = |φ 0|) := by
  /-
  CLOSER HOP 1 (partial). The fourth conjunct is now closed independently by
  `m03J03_abs_eval_not_distribution`: a compactly supported smooth bump equals
  one at zero, while distribution linearity sends its negation to the negative
  value, contradicting absolute evaluation.

  The first three distribution-construction clauses remain. Mathlib searches
  found useful constructors and Fourier operations for `TemperedDistribution`
  (including `TemperedDistribution.delta` and regular tempered
  distributions), but no compiled locally finite Dirac-sum constructor or
  polynomial-growth Fourier-series convergence theorem producing the
  `Distribution (⊤ : Opens ℝ) ℂ ⊤` required here.

  Renewed searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, the solved
  distribution corpus, Mathlib source, and git history found no constructor
  that resolves them. A direct proof must separately build continuous linear maps on the LF
  test-function space: local finiteness and compact-dependent seminorm bounds
  for the Dirac comb; `N + 2` integrations by parts and summability for the
  Fourier series; regular distributions plus two half-line integration-by-parts
  identities for `H * sin`; and a bundled test function nonzero at zero to
  refute linearity of `φ ↦ |φ 0|`. Pointwise formulas alone do not discharge
  the continuity fields of `Distribution`. No solved sibling contains this
  combined construction, so no sibling code was reused and the frozen
  statement was left unchanged.
  -/
  sorry

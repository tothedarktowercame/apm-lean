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

/-- Multiplication by the chosen Heaviside representative is exactly
restriction of the integral to the positive half-line. -/
lemma m03J03_integral_heaviside_mul (g : ℝ → ℝ) :
    (∫ x : ℝ, m03J03Heaviside x * g x) = ∫ x in Ioi (0 : ℝ), g x := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 < x <;> simp [m03J03Heaviside, hx]

/-- The first half-line integration-by-parts identity for `H * sin`. The
compact-support endpoint theorem removes both the value at infinity and the
zero endpoint, since `sin 0 = 0`. -/
lemma m03J03_heaviside_sin_integral_deriv
    (φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤) :
    -(∫ x : ℝ, m03J03Heaviside x * Real.sin x * deriv φ x) =
      ∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x := by
  let g : ℝ → ℝ := fun x ↦ Real.sin x * φ x
  have hg : ContDiff ℝ 1 g :=
    Real.contDiff_sin.mul (φ.contDiff.of_le (by simp))
  have hgc : HasCompactSupport g := φ.hasCompactSupport.mul_left
  have hderiv (x : ℝ) : deriv g x =
      Real.cos x * φ x + Real.sin x * deriv φ x := by
    have hs := Real.hasDerivAt_sin x
    have hφ := φ.contDiff.differentiable (by simp) x
    simpa [g] using (hs.mul hφ.hasDerivAt).deriv
  have hint := hgc.integral_Ioi_deriv_eq hg 0
  simp_rw [hderiv] at hint
  have hcos : IntegrableOn (fun x : ℝ ↦ Real.cos x * φ x) (Ioi 0) :=
    (Real.continuous_cos.mul φ.contDiff.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left |>.integrableOn
  have hsin : IntegrableOn (fun x : ℝ ↦ Real.sin x * deriv φ x) (Ioi 0) :=
    (Real.continuous_sin.mul
      (φ.contDiff.continuous_deriv (by simp))).integrable_of_hasCompactSupport
        φ.hasCompactSupport.deriv.mul_left |>.integrableOn
  rw [integral_add hcos hsin] at hint
  rw [show (∫ x : ℝ, m03J03Heaviside x * Real.sin x * deriv φ x) =
      ∫ x in Ioi (0 : ℝ), Real.sin x * deriv φ x by
        simpa [mul_assoc] using
          m03J03_integral_heaviside_mul (fun x ↦ Real.sin x * deriv φ x),
    show (∫ x : ℝ, m03J03Heaviside x * Real.cos x * φ x) =
      ∫ x in Ioi (0 : ℝ), Real.cos x * φ x by
        simpa [mul_assoc] using
          m03J03_integral_heaviside_mul (fun x ↦ Real.cos x * φ x)]
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0, neg_zero] at hint
  linarith

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

  CLOSER HOP 2: the Heaviside/set-integral conversion needed by both
  integration-by-parts identities is now compiled as
  `m03J03_integral_heaviside_mul`. It proves for an arbitrary real function
  `g` that integrating `m03J03Heaviside x * g x` over `ℝ` is definitionally
  the set integral over `Ioi 0`, by identifying the product a.e. with the
  indicator. This removes the discontinuous Heaviside representative from the
  remaining analytic calculation.

  Searches beyond hop 1 covered the improper-integral integration-by-parts
  theorems, compact-support multiplication/derivative APIs, and regular and
  tempered distribution constructors. The first group supplies the intended
  next route after the new reduction, but completing its endpoint-at-infinity
  limits and then bundling all three functionals as LF-continuous maps remains
  open. No packaged Dirac-comb or polynomial-growth Fourier-series constructor
  was found. The frozen statement remains unchanged.

  CLOSER HOP 3 closes the first derivative identity at function level.
  `m03J03_heaviside_sin_integral_deriv` applies the compact-support endpoint
  theorem directly to `g x = sin x * φ x`, proves the product derivative
  formula, and obtains `-∫ H sin φ' = ∫ H cos φ`. No explicit endpoint limit
  is needed.

  Renewed searches covered the countable sum-of-Dirac measure integral API,
  tempered-measure constructors, TestFunction-to-Schwartz maps, and siblings
  `m02J01` and `m95J05`. The sum-of-Dirac results compute integrals once
  summability is available, but do not establish local finiteness/temperate
  growth of the one-sided counting measure or construct the required
  LF-continuous `Distribution`. The remaining bridge is the second half-line
  identity, construction and LF-continuity of the three regular functionals,
  and the Dirac-comb/Fourier-series constructors. The frozen statement remains
  unchanged.
  -/
  sorry

import Mathlib

/-!
# APM a98A07

## Statement repairs

None.

## Encoding questions

None.  “Uniformly on compact subsets” is represented by Mathlib's
`TendstoLocallyUniformlyOn` predicate.
-/

open Filter MeasureTheory Metric Set
open scoped Topology

/-- The logarithm in the boundary majorant stays strictly negative throughout
the circle parameter interval. -/
lemma apm_a98A07_log_ratio_neg {t : ℝ}
    (ht : 0 < t) (htop : t < 2 * Real.pi) :
    Real.log (t / (4 * Real.pi)) < 0 := by
  apply Real.log_neg
  · positivity
  · apply (div_lt_one (by positivity : 0 < 4 * Real.pi)).2
    nlinarith [Real.pi_pos]

theorem apm_a98a07 :
    ∀ f : ℕ → ℂ → ℂ,
      (∃ U : Set ℂ,
        IsOpen U ∧ closedBall (0 : ℂ) 1 ⊆ U ∧
          ∀ n : ℕ, DifferentiableOn ℂ (f n) U) →
      (∀ (n : ℕ) (t : ℝ), 0 < t → t < 2 * Real.pi →
        ‖f n (Complex.exp (Complex.I * (t : ℂ)))‖ ≤
          1 / (t * (Real.log (t / (4 * Real.pi))) ^ 2)) →
      (∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) (2 * Real.pi))),
        ∃ w : ℂ,
          Tendsto (fun n : ℕ => f n (Complex.exp (Complex.I * (t : ℂ)))) atTop (𝓝 w)) →
      ∃ g : ℂ → ℂ,
        DifferentiableOn ℂ g (ball 0 1) ∧
        TendstoLocallyUniformlyOn f g atTop (ball 0 1) := by
  /-
  PARTIAL boundary (closer hop 1).

  `apm_a98A07_log_ratio_neg` now proves that
  `log (t/(4π)) < 0` throughout `(0,2π)`. This formally eliminates a second
  endpoint pole and isolates `t = 0` as the majorant's only singularity.

  Searches went beyond the original `Vitali` name: `LEMMA-INDEX.md`,
  `ConstructionTargets/`, closed artifacts, and Mathlib's locally-uniform,
  normal-family, compact-open, holomorphic-limit, Morera, Cauchy integral,
  Bochner dominated-convergence, and improper-log-integral sources contain no
  Vitali/Montel or Weierstrass convergence theorem matching
  `TendstoLocallyUniformlyOn`. Mathlib's Cauchy formula can reconstruct each
  `f n`, but the frozen boundary data are merely a.e. convergent under an L¹
  majorant, so closure still requires: prove integrability of
  `1/(t*log(t/(4π))²)` by logarithmic substitution; select a measurable a.e.
  limit; obtain L¹ convergence by DCT; establish a uniform Cauchy-kernel bound
  on each compact subdisk; and prove the locally uniform limit holomorphic.

  Related Hurwitz/Rouché artifacts (`a97J08`, `a94A09`) confirm the absence of
  the final holomorphic-limit pipeline, and git history has no later attempt.
  No statement defect was found.
  -/
  sorry

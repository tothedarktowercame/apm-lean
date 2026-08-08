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

/-- The real boundary majorant from the frozen hypothesis. -/
noncomputable def apm_a98A07_majorant (t : ℝ) : ℝ :=
  1 / (t * (Real.log (t / (4 * Real.pi))) ^ 2)

/-- The logarithm in the boundary majorant stays strictly negative throughout
the circle parameter interval. -/
lemma apm_a98A07_log_ratio_neg {t : ℝ}
    (ht : 0 < t) (htop : t < 2 * Real.pi) :
    Real.log (t / (4 * Real.pi)) < 0 := by
  apply Real.log_neg
  · positivity
  · apply (div_lt_one (by positivity : 0 < 4 * Real.pi)).2
    nlinarith [Real.pi_pos]

/-- The majorant is strictly positive throughout the boundary parameter
interval. -/
lemma apm_a98A07_majorant_pos {t : ℝ}
    (ht : 0 < t) (htop : t < 2 * Real.pi) :
    0 < apm_a98A07_majorant t := by
  rw [apm_a98A07_majorant]
  apply one_div_pos.mpr
  exact mul_pos ht (sq_pos_of_neg (apm_a98A07_log_ratio_neg ht htop))

/-- The boundary majorant is measurable, so once its logarithmic improper
integral is established it can be used directly by dominated convergence. -/
lemma apm_a98A07_majorant_measurable :
    Measurable apm_a98A07_majorant := by
  unfold apm_a98A07_majorant
  fun_prop

/-- Mathlib's Weierstrass theorem closes the final regularity step once local
uniform convergence on the disk has been constructed. -/
lemma apm_a98A07_differentiableOn_of_locallyUniform
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1))
    (hconv : TendstoLocallyUniformlyOn f g atTop (ball 0 1)) :
    DifferentiableOn ℂ g (ball 0 1) := by
  exact hconv.differentiableOn (Eventually.of_forall hf) isOpen_ball

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
  PARTIAL boundary (closer hop 3).

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

  CLOSER HOP 2: the prior claim that Mathlib lacked the final holomorphic-limit
  pipeline is now obsolete. `Analysis.Complex.LocallyUniformLimit` provides
  `TendstoLocallyUniformlyOn.differentiableOn`, and sibling `a01A07` contains a
  compiled use of exactly that theorem. The helper
  `apm_a98A07_differentiableOn_of_locallyUniform` above adapts it to this unit
  disk, closing step 4 completely. The remaining bridge is now only steps 1--3:
  majorant integrability, boundary L¹ convergence, and the Cauchy-kernel bound
  producing local uniform convergence.

  CLOSER HOP 3: the displayed bound is now packaged as
  `apm_a98A07_majorant`. `apm_a98A07_majorant_measurable` proves its global
  measurability, and `apm_a98A07_majorant_pos` combines the strict logarithm
  sign from hop 1 with the positive parameter to prove strict positivity on
  `(0,2π)`. These discharge the measurability and sign obligations needed by
  dominated convergence. Searches of the improper-log-integral and
  one-dimensional substitution APIs still found no packaged evaluation of
  `1/(t*log(t/(4π))²)`; proving its integrability by `u = -log(t/(4π))`, then
  selecting the measurable a.e. limit and deriving the Cauchy-kernel bound,
  remains open.
  -/
  sorry

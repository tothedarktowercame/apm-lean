import Mathlib

/-!
# APM m94A03

## Statement repairs

None.

## Encoding notes

The ambient space is the genuine Euclidean space `ℝⁿ`.  Sobolev membership is
encoded from first principles using `L²` membership and an `L²` weak gradient,
tested against smooth compactly supported scalar functions on the unit ball.
The totalized value `Real.log 0 = 0` only chooses a representative at the
measure-zero singular point.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

noncomputable def apm_m94a03_logNorm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.log ‖x‖

/-- The classical gradient of `log ‖x‖`, totalized at the origin. -/
noncomputable def apm_m94a03_logNormGradient {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖x‖⁻¹ ^ 2 • x

lemma apm_m94a03_norm_logNormGradient {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖apm_m94a03_logNormGradient x‖ = ‖x‖⁻¹ := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [apm_m94a03_logNormGradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  field_simp

/-- The norm formula also holds at the totalized origin, where both sides are
zero. This removes the exceptional point from later `L²` calculations. -/
lemma apm_m94a03_norm_logNormGradient_all {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖apm_m94a03_logNormGradient x‖ = ‖x‖⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [apm_m94a03_logNormGradient]
  · exact apm_m94a03_norm_logNormGradient hx

/-- The totalized logarithmic representative is strongly measurable. -/
lemma apm_m94a03_logNorm_aestronglyMeasurable {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} :
    AEStronglyMeasurable
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin n) → ℝ) μ := by
  exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable

/-- The totalized classical gradient is strongly measurable. -/
lemma apm_m94a03_logNormGradient_aestronglyMeasurable {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} :
    AEStronglyMeasurable
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) μ := by
  apply Measurable.aestronglyMeasurable
  exact ((measurable_norm.inv.pow_const 2).smul measurable_id)

/-- Square-integrability (indeed `Lᵖ` membership for any exponent) of the
vector candidate is exactly the scalar radial integrability problem. -/
lemma apm_m94a03_logNormGradient_memLp_iff {n : ℕ} {p : ℝ≥0∞}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} :
    MemLp (apm_m94a03_logNormGradient :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) p μ ↔
      MemLp (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖⁻¹) p μ := by
  apply memLp_congr_norm
  · exact apm_m94a03_logNormGradient_aestronglyMeasurable
  · exact measurable_norm.inv.aestronglyMeasurable
  · filter_upwards with x
    rw [apm_m94a03_norm_logNormGradient_all, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]

def apm_m94a03_IsWeakGradientOn {n : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ → Function.support φ ⊆ s →
      ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)
          ∂(volume.restrict s) =
        -∫ x, (g x i) * φ x ∂(volume.restrict s)

def apm_m94a03_InH1UnitBall (n : ℕ) : Prop :=
  let E := EuclideanSpace ℝ (Fin n)
  let Ω : Set E := Metric.ball 0 1
  MemLp (apm_m94a03_logNorm : E → ℝ) 2 (volume.restrict Ω) ∧
  ∃ g : E → E, MemLp g 2 (volume.restrict Ω) ∧
    apm_m94a03_IsWeakGradientOn Ω apm_m94a03_logNorm g

theorem apm_m94a03 :
    ¬ apm_m94a03_InH1UnitBall 2 ∧
    apm_m94a03_InH1UnitBall 3 ∧
    apm_m94a03_InH1UnitBall 4 := by
  /-
  CLOSER HOP 1 (partial). The classical candidate gradient is now defined by
  `apm_m94a03_logNormGradient`, and
  `apm_m94a03_norm_logNormGradient` proves its exact norm is `‖x‖⁻¹` away
  from zero. Thus its squared radial singularity is pinned for both the
  positive and negative dimension thresholds.

  The remaining boundary: the positive cases require proving radial `L²` integrability of
  `log ‖x‖` and of the candidate gradient `x / ‖x‖ ^ 2` in dimensions three
  and four, then establishing the custom weak-gradient identity by integrating
  over a punctured ball and showing the inner-sphere boundary term tends to
  zero. The negative two-dimensional case additionally requires uniqueness of
  distributional weak gradients, so that any hypothetical `L²` gradient is
  identified almost everywhere with the non-square-integrable classical
  gradient away from zero.

  Renewed searches of Mathlib and the repository for radial/polar integration and weak
  derivative infrastructure. The repository has a specialized three-
  dimensional radial integral construction in `a95A03`, but no general
  dimension-two/four formula or compiled route for this custom Euclidean-space
  weak-gradient predicate. I did not complete the punctured-domain divergence
  theorem, boundary-limit, and weak-gradient uniqueness machinery required by
  all three conjuncts within this pass. `Complex.integral_comp_polarCoord_symm`
  covers dimension two after an isometric transport, but no corresponding
  ready-made general Euclidean radial formula or weak-gradient uniqueness
  theorem was found in `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
  siblings, or git history.

  Closer hop 2 removes the measurability and vector-to-scalar interfaces from
  the remaining radial problem. `apm_m94a03_norm_logNormGradient_all` extends
  the norm identity through the totalized origin. The two measurable helpers
  prove strong measurability for arbitrary ambient measures, and
  `apm_m94a03_logNormGradient_memLp_iff` uses `memLp_congr_norm` to show that
  the vector candidate belongs to any `Lᵖ(μ)` exactly when the scalar function
  `x ↦ ‖x‖⁻¹` does. Thus no a.e.-exception or coordinatewise measurability
  bookkeeping remains in the dimension threshold.

  Further searches covered Mathlib's norm-derivative, Euclidean inner-product,
  `MemLp`, Hausdorff/radial, and divergence-theorem APIs, plus the radial
  artifacts `a95A03` and `m95J02`. They provide local derivative and
  specialized radial ingredients but still no dimension-parametric formula
  for the restricted unit ball. The remaining bridges are now the scalar
  radial integrals, punctured-ball integration by parts, and weak-gradient
  uniqueness in dimension two. The frozen statement is unchanged.
  -/
  sorry

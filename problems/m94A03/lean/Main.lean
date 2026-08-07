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
  -/
  sorry

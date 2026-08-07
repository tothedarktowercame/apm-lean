import Mathlib

/-!
# APM m94J04

## Statement repairs

The printed cases `f=y` if `x>0` and `f=x` if `z<0` overlap on
`{x>0,z<0}` and leave `{x≤0,z≥0}` undefined. Following the intended
single-interface computation, the second condition is repaired to `x≤0`.
Thus the jump is across the plane `x=0`.

## Encoding questions

The distributional identity is stated against every compactly supported smooth
vector test function on `ℝ³`. The left side is the weak curl pairing and the
right side is the regular distribution represented by `(0,0,-1_{x>0})`.
-/

open MeasureTheory
open scoped Distributions

abbrev apm_m94J04_E := EuclideanSpace ℝ (Fin 3)

/-- Coordinate vector in `ℝ³`. -/
noncomputable def apm_m94J04_basis (i : Fin 3) : apm_m94J04_E :=
  EuclideanSpace.single i 1

/-- The repaired scalar field from the problem. -/
noncomputable def apm_m94J04_f (p : apm_m94J04_E) : ℝ :=
  if 0 < p 0 then p 1 else p 0

/-- The vector field `u=f e₁`. -/
noncomputable def apm_m94J04_u (p : apm_m94J04_E) : apm_m94J04_E :=
  apm_m94J04_f p • apm_m94J04_basis 0

/-- Classical curl of a smooth vector-valued test function. -/
noncomputable def apm_m94J04_curlTest
    (φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) : apm_m94J04_E :=
  (fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 1) -
      fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 2)) • apm_m94J04_basis 0 +
  (fderiv ℝ (fun q ↦ φ q 0) p (apm_m94J04_basis 2) -
      fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 0)) • apm_m94J04_basis 1 +
  (fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 0) -
      fderiv ℝ (fun q ↦ φ q 0) p (apm_m94J04_basis 1)) • apm_m94J04_basis 2

/-- The regular field representing the claimed distributional curl. -/
noncomputable def apm_m94J04_curlValue (p : apm_m94J04_E) : apm_m94J04_E :=
  (if 0 < p 0 then (-1 : ℝ) else 0) • apm_m94J04_basis 2

theorem apm_m94j04 :
    ∀ φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤,
      ∫ p, inner ℝ (apm_m94J04_u p) (apm_m94J04_curlTest φ p) ∂volume =
        ∫ p, inner ℝ (apm_m94J04_curlValue p) (φ p) ∂volume := by
  /-
  Boundary: after expanding the Euclidean basis and inner products, the
  identity reduces fiberwise to `∫ y * ∂y φ₂ = -∫ φ₂` on `x > 0` and
  `∫ x * ∂y φ₂ = 0` on `x ≤ 0`. I searched Mathlib for the global
  line-derivative integration-by-parts API, including
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` and
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`. Their
  differentiability hypotheses apply on `tsupport` in the whole ambient
  space, so they cannot be applied directly to the coefficient
  `if 0 < x then y else x`, which is not differentiable on `x = 0`.

  `TestFunction.contDiff`, `TestFunction.hasCompactSupport`, and
  `Continuous.integrable_of_hasCompactSupport` provide the local smoothness
  and integrability ingredients. The remaining blocker is the measure bridge:
  decompose Euclidean `volume` into `(x,z)` and `y` fibers, transport the
  compact support and `fderiv` to each slice, apply one-dimensional integration
  by parts, and reassemble with `MeasureTheory.integral_prod`. Searches of all
  closed problem artifacts, `ConstructionTargets`, `YoungL2.lean`, boundary
  comments, and git history found Fubini patterns but no proved lemma packaging
  this Euclidean-coordinate slicing step.
  -/
  sorry

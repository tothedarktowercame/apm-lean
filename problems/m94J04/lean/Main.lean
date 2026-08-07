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

lemma apm_m94J04_f_of_pos {p : apm_m94J04_E} (hp : 0 < p 0) :
    apm_m94J04_f p = p 1 := by
  simp [apm_m94J04_f, hp]

lemma apm_m94J04_f_of_nonpos {p : apm_m94J04_E} (hp : p 0 ≤ 0) :
    apm_m94J04_f p = p 0 := by
  simp [apm_m94J04_f, not_lt.mpr hp]

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

/-- Coordinate reduction of the weak-curl integrand. -/
lemma apm_m94J04_inner_u_curlTest
    (φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) :
    inner ℝ (apm_m94J04_u p) (apm_m94J04_curlTest φ p) =
      apm_m94J04_f p *
        (fderiv ℝ (fun q ↦ φ q 2) p (apm_m94J04_basis 1) -
          fderiv ℝ (fun q ↦ φ q 1) p (apm_m94J04_basis 2)) := by
  rw [apm_m94J04_u, apm_m94J04_curlTest, inner_smul_left]
  simp [apm_m94J04_basis, inner_add_right, inner_smul_right,
    PiLp.inner_apply, Fin.sum_univ_succ]

/-- Coordinate reduction of the claimed regular curl. -/
lemma apm_m94J04_inner_curlValue
    (φ : apm_m94J04_E → apm_m94J04_E) (p : apm_m94J04_E) :
    inner ℝ (apm_m94J04_curlValue p) (φ p) =
      (if 0 < p 0 then -φ p 2 else 0) := by
  have hone (x : ℝ) : inner ℝ 1 x = x := by
    rw [show x = x • (1 : ℝ) by simp, real_inner_smul_right]
    norm_num
  rw [apm_m94J04_curlValue]
  split_ifs <;>
    simp [apm_m94J04_basis, PiLp.inner_apply, Fin.sum_univ_succ, hone]

theorem apm_m94j04 :
    ∀ φ : TestFunction (⊤ : TopologicalSpace.Opens apm_m94J04_E)
      apm_m94J04_E ⊤,
      ∫ p, inner ℝ (apm_m94J04_u p) (apm_m94J04_curlTest φ p) ∂volume =
        ∫ p, inner ℝ (apm_m94J04_curlValue p) (φ p) ∂volume := by
  intro φ
  simp_rw [apm_m94J04_inner_u_curlTest, apm_m94J04_inner_curlValue]
  /-
  PASS-1 boundary (Codex): the Euclidean basis and inner-product algebra is
  now completely discharged by the two proved helpers above. The remaining
  scalar identity is fiberwise `∫ y * ∂y φ₂ = -∫ φ₂` on `x > 0`, together
  with `∫ x * ∂y φ₂ = 0` and the analogous z-derivative integral on `x ≤ 0`.

  APIs searched: `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`,
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`, `integral_prod`,
  `volume_pi`, `MeasurePreserving.piFinSuccAbove`, and the one-dimensional
  `intervalIntegral.integral_deriv_of_contDiffOn_Icc`. The global
  line-derivative integration-by-parts lemmas have differentiability
  hypotheses on `tsupport` in the whole ambient
  space, so they cannot be applied directly to the coefficient
  `if 0 < x then y else x`, which is not differentiable on `x = 0`.

  `TestFunction.contDiff`, `TestFunction.hasCompactSupport`, and
  `Continuous.integrable_of_hasCompactSupport` provide the local smoothness
  and integrability ingredients. I additionally searched `LEMMA-INDEX.md`
  (1037 indexed helpers) and all 170 currently closed artifacts. The nearest
  Fubini examples (`a94J04`, `a02J01`, and
  `ConstructionTargets.YoungConvolution`) establish product-integral patterns,
  but none transports Euclidean `volume` through the coordinate split while
  identifying the slice derivative. The unresolved bridge is therefore to use
  `volume_pi`, split `Fin 3` around coordinate 1 (and coordinate 2), transport
  compact support and `fderiv` to each real slice, apply one-dimensional
  integration by parts, and reassemble with `MeasureTheory.integral_prod`.

  Closer hop 1 proves the coefficient branch normal forms
  `apm_m94J04_f_of_pos` and `apm_m94J04_f_of_nonpos`. A renewed source search
  finds `EuclideanSpace.volume_preserving_measurableEquiv_toLp` (used in
  solved artifact `a01A01`) as the missing first transport from the `WithLp`
  Euclidean representation to the raw coordinate function space. After that,
  `MeasurePreserving.piFinSuccAbove` and `volume_pi` can isolate a coordinate.
  The general `MeasureTheory.Integral.DivergenceTheorem` was inspected but is
  not directly applicable because the scalar coefficient is discontinuous at
  `x = 0`; the line-derivative integration-by-parts theorem has the same
  ambient differentiability obstruction.

  No `LEMMA-INDEX.md`, `ConstructionTargets/`, sibling, or git-history result
  packages the composite `WithLp → Pi → coordinate × complement` measure
  equivalence together with the sliced `fderiv` identity. That transport and
  its compact-support/integrability consequences remain the precise live
  bridge. The frozen statement was left unchanged.
  -/
  sorry

import Mathlib
import ConstructionTargets.t96A06Closure
import ConstructionTargets.CoefficientCoveringTransfer
import ConstructionTargets.CoefficientSphereAntipodal
import ConstructionTargets.CoefficientFirstReflection

/-! # Rational homology of ℝP³ (design claude-14, 2026-10-15)

`H_k(ℝP³; ℚ) = ℚ, 0, 0, ℚ, 0, …` for the literal `Space ℝ 3`, by transfer through the
double cover `S³ → ℝP³` (plan C2 of `ConstructionTargets/t96A06Closure.blueprint.md`):

* `p : S³ → ℝP³`, `x ↦ [x]`, is a 2-sheeted cover (`proj_cover`).
* Transfer then projection is `2 • 𝟙` on `H_k(ℝP³)` (banked
  `CoefficientCoveringTransfer.rational_homology_projection`), so `H_k(ℝP³)` is a retract of
  `H_k(S³)`: it vanishes wherever `H_k(S³)` does (`retract_isZero`, `sphere_isZero`).
* Projection then transfer is `𝟙 + a_*` on `H_k(S³)` (the two lifts of `p ∘ σ` are `σ` and
  `a ∘ σ`; `proj_transfer`).  On `H₃(S³)` the antipodal map acts as `+1` (banked
  `antipodal_action`, `(-1)^4 = 1`), so `p_*` is an isomorphism on `H₃` (`h3_iso`).
* `H₀` is banked (`t96A06Closure.rp3RationalH0Iso`), `H₃(S³) ≅ ℚ` is banked (`topIso ℚ 2`).

Consumers: t96J07 (`apm_t96j07_global_rationalHomology_bases`) and t96A06 (finiteness,
vanishing, traces on `H₀..H₂`). -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open ConstructionTargets ConstructionTargets.ProjectiveSpaceTopology T02A06

namespace RP3Homology

abbrev S3 := T02A06.euclideanUnitSphere 4
abbrev RP3 := ConstructionTargets.t96A06Closure.RP3

/-- Rational singular homology. -/
abbrev HQ (k : ℕ) (X : Type) [TopologicalSpace X] :=
  ConstructionTargets.CoefficientH0.SingularHomology ℚ k (TopCat.of X)

/-- The projection `S³ → ℝP³`. -/
def projFun (x : S3) : RP3 :=
  Projectivization.mk ℝ ((WithLp.equiv 2 (Fin 4 → ℝ)) x.1) (by
    intro h
    have hx : x.1 = 0 := (WithLp.equiv 2 (Fin 4 → ℝ)).injective (by simpa using h)
    have := x.2
    simp [hx] at this)

/-- The antipodal map of `S³`. -/
abbrev antipodal : C(S3, S3) := ConstructionTargets.CoefficientSphereAntipodal.antipodal (d := 4)

/-- `S³ → ℝP³` is a 2-sheeted covering (fibres `{x, -x}`; local sections over the affine
charts `vᵢ ≠ 0`, or via Mathlib's quotient-covering criterion for the `±1` action). -/
theorem proj_cover : CoveringDegree.IsKSheetedCover projFun 2 := by
  sorry

/-- Rational homology of `S³` vanishes in positive degrees other than `3` (iterate
`CoefficientSphereShift.sphereShift` down to `S¹`/`S⁰`). -/
theorem sphere_isZero (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) : IsZero (HQ k S3) := by
  sorry

/-- `H₃(S³; ℚ) ≅ ℚ` (banked `CoefficientFirstReflection.topIso ℚ 2`). -/
theorem sphere_top : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ) := by
  sorry

/-- Base homology is a retract of total-space homology for a 2-sheeted cover, over `ℚ`
(banked `rational_homology_projection`: transfer ≫ p_* = 2 • 𝟙). -/
theorem retract_isZero (hcov : CoveringDegree.IsKSheetedCover projFun 2) (k : ℕ)
    (hS : IsZero (HQ k S3)) : IsZero (HQ k RP3) := by
  sorry

/-- Projection then transfer is `𝟙 + a_*`: the lifts of `p ∘ σ` are exactly `σ` and `a ∘ σ`. -/
-- BEGIN SEAT AREA
theorem proj_transfer (hcov : CoveringDegree.IsKSheetedCover projFun 2) (k : ℕ) :
    HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ ⟨projFun, hcov.isCoveringMap.continuous⟩) k ≫
      HomologicalComplex.homologyMap (CoefficientCoveringTransfer.transfer ℚ projFun hcov) k =
    𝟙 _ + HomologicalComplex.homologyMap (CoefficientH0.singularPostcomposition ℚ antipodal) k := by
  sorry
-- END SEAT AREA

/-- `p_*` is an isomorphism on `H₃`: `τ ≫ p_* = 2 • 𝟙` and `p_* ≫ τ = 𝟙 + a_* = 2 • 𝟙`
(`antipodal_action ℚ 3`). -/
theorem h3_iso (hcov : CoveringDegree.IsKSheetedCover projFun 2)
    (hpt : HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ ⟨projFun, hcov.isCoveringMap.continuous⟩) 3 ≫
      HomologicalComplex.homologyMap (CoefficientCoveringTransfer.transfer ℚ projFun hcov) 3 =
      𝟙 _ + HomologicalComplex.homologyMap
        (CoefficientH0.singularPostcomposition ℚ antipodal) 3)
    (htop : Nonempty (HQ 3 S3 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (HQ 3 RP3 ≅ ModuleCat.of ℚ ℚ) := by
  sorry

/-- The result. -/
theorem rp3_rationalHomology :
    Nonempty (HQ 0 RP3 ≅ ModuleCat.of ℚ ℚ) ∧
    (∀ k, k ≠ 0 → k ≠ 3 → IsZero (HQ k RP3)) ∧
    Nonempty (HQ 3 RP3 ≅ ModuleCat.of ℚ ℚ) := by
  have hcov := proj_cover
  refine ⟨⟨ConstructionTargets.t96A06Closure.rp3RationalH0Iso⟩, fun k hk0 hk3 =>
    retract_isZero hcov k (sphere_isZero k hk0 hk3), ?_⟩
  exact h3_iso hcov (proj_transfer hcov 3) sphere_top

end RP3Homology

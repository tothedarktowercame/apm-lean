import ConstructionTargets.SardFirstDerivativeProjectedChartFormula
import ConstructionTargets.SardLocalRankNormalForm
import ConstructionTargets.SardProjectedComplementedStrictDerivativeData
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Filter
open scoped Topology
noncomputable section
namespace SardFirstDerivativeProjectedChartInverseFormulaProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local instance derivativeRangeCompleteSpace (L : E →L[ℝ] F) :
    CompleteSpace (LinearMap.range L.toLinearMap) := by
  letI := L.toLinearMap.finiteDimensional_range
  exact (LinearMap.range L.toLinearMap).complete_of_finiteDimensional.completeSpace_coe

/-- The exact projected rank chart retains both its forward formula and its
local inverse-coordinate identities near the base coordinate. -/
theorem exists_projected_localRankNormalForm_with_inverse_formula
    (f : E → F) (x : E) (L : E →L[ℝ] F) (hf : HasStrictFDerivAt f L x) :
    let R := LinearMap.range L.toLinearMap
    let A : E →L[ℝ] R := R.orthogonalProjection.comp L
    let G := A.ker
    ∃ e : OpenPartialHomeomorph E (R × G),
      x ∈ e.source ∧
      (e : E → R × G) =
        (fun y => (R.orthogonalProjection (f y), G.orthogonalProjection y)) ∧
      (∀ᶠ p : R × G in 𝓝 (R.orthogonalProjection (f x), G.orthogonalProjection x),
        R.orthogonalProjection (f (e.symm p)) = p.1 ∧
          G.orthogonalProjection (e.symm p) = p.2) := by
  dsimp only
  let R := LinearMap.range L.toLinearMap
  let hR : CompleteSpace R := by
    letI := L.toLinearMap.finiteDimensional_range
    exact R.complete_of_finiteDimensional.completeSpace_coe
  letI := hR
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  let G := A.ker
  let hG : CompleteSpace G := by infer_instance
  letI := hG
  let B : E →L[ℝ] G := G.orthogonalProjection
  have h := SardProjectedImplicitFunctionDataProbe.projected_complemented_strictDerivative_data
    f x L hf
  let φ := @ImplicitFunctionData.mk ℝ inferInstance E inferInstance inferInstance inferInstance
    R inferInstance inferInstance hR G inferInstance inferInstance hG
    (fun y => R.orthogonalProjection (f y)) A
    (fun y => G.orthogonalProjection y) B x h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  exact @localRankNormalForm_of_complemented_minor E R G inferInstance inferInstance
    inferInstance inferInstance inferInstance hR inferInstance inferInstance hG φ

#print axioms exists_projected_localRankNormalForm_with_inverse_formula

end SardFirstDerivativeProjectedChartInverseFormulaProbe

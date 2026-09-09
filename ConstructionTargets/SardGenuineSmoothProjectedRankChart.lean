import ConstructionTargets.SardProjectedComplementedStrictDerivativeData
import ConstructionTargets.SardSmoothNeighborhoodImplicitChart
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped ContDiff
noncomputable section
namespace SardGenuineSmoothProjectedRankChartProbe
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_genuine_smooth_projected_rank_chart
    (f : E → F) (x : E) (hf : ContDiff ℝ ∞ f) :
    let L := fderiv ℝ f x
    let R := LinearMap.range L.toLinearMap
    letI hR : CompleteSpace R := by infer_instance
    let A := R.orthogonalProjection.comp L
    let G := A.ker
    letI hG : CompleteSpace G := by infer_instance
    ∃ (φ : @ImplicitFunctionData ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG) (e : OpenPartialHomeomorph E (R × G)),
      (@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) = (fun y => R.orthogonalProjection (f y)) ∧
      (@ImplicitFunctionData.leftDeriv ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) = A ∧
      (@ImplicitFunctionData.rightFun ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) = (fun y => G.orthogonalProjection y) ∧
      (@ImplicitFunctionData.rightDeriv ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) = G.orthogonalProjection ∧
      (@ImplicitFunctionData.pt ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) = x ∧
      x ∈ e.source ∧ e.source ⊆ (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ).source ∧
      (e : E → R × G) = (fun y => (R.orthogonalProjection (f y), G.orthogonalProjection y)) ∧
      (∀ y ∈ e.target, e.symm y = (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ).symm y) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ y, (e y).1 = R.orthogonalProjection (f y)) ∧
      (∀ r z, z ∈ {z | (r,z) ∈ e.target} →
        ContDiffAt ℝ ∞ (fun w : G => Rᗮ.orthogonalProjection (f (e.symm (r,w)))) z) := by
  dsimp only
  let L := fderiv ℝ f x
  let R := LinearMap.range L.toLinearMap
  letI hR : CompleteSpace R := by infer_instance
  let A := R.orthogonalProjection.comp L
  let G := A.ker
  letI hG : CompleteSpace G := by infer_instance
  have hstrict : HasStrictFDerivAt f L x := hf.contDiffAt.hasStrictFDerivAt (by simp)
  have h := SardProjectedImplicitFunctionDataProbe.projected_complemented_strictDerivative_data f x L hstrict
  let φ := @ImplicitFunctionData.mk ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG
    (fun y => R.orthogonalProjection (f y)) A
    (fun y => G.orthogonalProjection y) G.orthogonalProjection x
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  have hl : ContDiffOn ℝ ∞ (@ImplicitFunctionData.leftFun ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ).source :=
    (R.orthogonalProjection.contDiff.comp hf).contDiffOn
  have hr : ContDiffOn ℝ ∞ (@ImplicitFunctionData.rightFun ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ).source :=
    G.orthogonalProjection.contDiff.contDiffOn
  obtain ⟨e, he, _, hsource, hforward, hinverse, hsm, hsi⟩ :=
    @SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_implicit_chart
      E R G inferInstance inferInstance inferInstance inferInstance inferInstance hR
      inferInstance inferInstance hG φ (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ).source
      (@ImplicitFunctionData.toOpenPartialHomeomorph ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ).open_source
      (@ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source ℝ inferInstance E inferInstance inferInstance inferInstance R inferInstance inferInstance hR G inferInstance inferInstance hG φ) (fun _ hz => hz) hl hr
  have heq : (e : E → R × G) = (fun y => (R.orthogonalProjection (f y), G.orthogonalProjection y)) := hforward
  refine ⟨φ, e, rfl, rfl, rfl, rfl, rfl, he, hsource, heq, hinverse, hsm, hsi, ?_, ?_⟩
  · intro y
    exact congrArg Prod.fst (congrFun heq y)
  · exact SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
      e f Rᗮ.orthogonalProjection ∞ hsi hf.contDiffOn

#print axioms exists_genuine_smooth_projected_rank_chart
end SardGenuineSmoothProjectedRankChartProbe

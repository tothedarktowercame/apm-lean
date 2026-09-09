import ConstructionTargets.RegularFiberChart
import ConstructionTargets.SardSmoothNeighborhoodImplicitChart
open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace ConstructionTargets.SmoothRegularFiberCoordinates
open RegularFiberChart
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (f : E → F) (L : E →L[ℝ] F) (x : E)
  (hf : HasStrictFDerivAt f L x) (hs : Function.Surjective L)
  (hsm : ContDiff ℝ ∞ f)
include hsm in
theorem exists_coordinates :
    ∃ e : OpenPartialHomeomorph E (F × L.ker),
      x ∈ e.source ∧ e.source ⊆ (base f L x hf hs).source ∧
      (e : E → F × L.ker) = base f L x hf hs ∧
      (∀ y ∈ e.target, e.symm y = (base f L x hf hs).symm y) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  letI : CompleteSpace L.ker := L.isClosed_ker.completeSpace_coe
  letI : CompleteSpace (F × L.ker) := inferInstance
  let P := kernelProjection L
  let D : E ≃L[ℝ] (F × L.ker) := (LinearMap.equivProdOfSurjectiveOfIsCompl L P
    (LinearMap.range_eq_top.mpr hs)
    (LinearMap.range_eq_of_proj (kernelProjection_retract L)) (kernel_complement L)).toContinuousLinearEquiv
  have hD : HasFDerivAt (base f L x hf hs) (D : E →L[ℝ] (F × L.ker)) x := by
    change HasFDerivAt (fun y => (f y-f x, P (y-x))) (L.prod P) x
    simpa only [ContinuousLinearMap.comp_id, id_eq] using ((hf.sub_const (f x)).prodMk
      (P.hasStrictFDerivAt.comp x ((hasStrictFDerivAt_id x).sub_const x))).hasFDerivAt
  have hsm' : ContDiff ℝ ∞ (base f L x hf hs) :=
    (hsm.sub contDiff_const).prodMk (P.contDiff.comp (contDiff_id.sub contDiff_const))
  obtain ⟨e, hx, _, he, hcoe, hinv, hfor, hback⟩ :=
    SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_neighborhood_restriction
      (base f L x hf hs) (base f L x hf hs).source
      (base f L x hf hs).open_source x (center_mem f L x hf hs) subset_rfl
      hsm'.contDiffOn D hD
  exact ⟨e, hx, he, hcoe, hinv, hfor, hback⟩
include hf hs hsm in
theorem exists_smooth_fiber_slice :
    ∃ e : OpenPartialHomeomorph E (F × L.ker),
      x ∈ e.source ∧ e x = (0,0) ∧
      (∀ y, (e y).1 = f y-f x) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      IsOpen {z : L.ker | (0,z) ∈ e.target} ∧
      (0 : L.ker) ∈ {z : L.ker | (0,z) ∈ e.target} ∧
      (fun z : L.ker => e.symm (0,z)) '' {z | (0,z) ∈ e.target} =
        e.source ∩ {y | f y = f x} ∧
      ContDiffOn ℝ ∞ (fun z : L.ker => e.symm (0,z)) {z | (0,z) ∈ e.target} ∧
      HasStrictFDerivAt (fun z : L.ker => e.symm (0,z)) L.ker.subtypeL 0 := by
  obtain ⟨e, hx, _, hcoe, hinv, hfor, hback⟩ := exists_coordinates f L x hf hs hsm
  have hcenter : e x = (0,0) := by rw [hcoe]; exact base_center f L x hf hs
  have hzero : (0, (0 : L.ker)) ∈ e.target := hcenter ▸ e.map_source hx
  have hopen : IsOpen {z : L.ker | (0,z) ∈ e.target} :=
    e.open_target.preimage (continuous_const.prodMk continuous_id)
  refine ⟨e, hx, hcenter, ?_, hfor, hback, hopen, hzero, ?_, ?_, ?_⟩
  · intro y; rw [hcoe]; rfl
  · have h := SardImplicitFunctionLevelSetKernelParameterizationProbe.OpenPartialHomeomorph.image_symm_mk_left_eq_inter_source_fst e (0 : F)
    simpa only [hcoe, base_fst, sub_eq_zero] using h
  · exact hback.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz)
  · apply (param_derivative f L x hf hs).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hzero] with z hz
    exact (hinv (0,z) hz).symm
#print axioms exists_coordinates
#print axioms exists_smooth_fiber_slice
end ConstructionTargets.SmoothRegularFiberCoordinates

import ConstructionTargets.SardOpenPartialHomeomorphContDiffOnSymm
import ConstructionTargets.SardProjectedChartResidualSlicesContDiffOn
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

open Set Filter
open scoped ContDiff Topology
noncomputable section
namespace SardSmoothNeighborhoodImplicitChartProbe

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace F] in
theorem exists_smooth_neighborhood_restriction
    (chart : OpenPartialHomeomorph E F) (U : Set E) (hU : IsOpen U)
    (x : E) (hx : x ∈ U) (hUs : U ⊆ chart.source)
    (hf : ContDiffOn ℝ ∞ chart U)
    (D : E ≃L[ℝ] F) (hD : HasFDerivAt chart (D : E →L[ℝ] F) x) :
    ∃ e : OpenPartialHomeomorph E F,
      x ∈ e.source ∧ e.source ⊆ U ∧ e.source ⊆ chart.source ∧
      (e : E → F) = chart ∧ (∀ y ∈ e.target, e.symm y = chart.symm y) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hc : ContinuousAt (fderiv ℝ (chart : E → F)) x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).continuousAt_fderiv (by simp)
  have hmem : fderiv ℝ (chart : E → F) x ∈ Set.range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F) :=
    ⟨D, hD.fderiv.symm⟩
  have hn := hc.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds hmem)
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) hn)
  let e := chart.restr V
  have hsource : e.source = chart.source ∩ V := chart.restr_source' V hVopen
  have heU : e.source ⊆ U := fun z hz => (hVsub ((hsource ▸ hz).2)).1
  have heS : e.source ⊆ chart.source := by rw [hsource]; exact inter_subset_left
  have hecoe : (e : E → F) = chart := rfl
  have hef : ContDiffOn ℝ ∞ e e.source := by rw [hecoe]; exact hf.mono heU
  refine ⟨e, ?_, heU, heS, hecoe, ?_, hef, ?_⟩
  · rw [hsource]; exact ⟨hUs hx, hxV⟩
  · intro y hy; rfl
  · apply SardOpenPartialHomeomorphContDiffOnSymmProbe.contDiffOn_symm_of_forall_hasFDerivAt_equiv e ∞ hef
    intro z hz
    obtain ⟨Dz, hDz⟩ := (hVsub ((hsource ▸ hz).2)).2
    refine ⟨Dz, ?_⟩
    rw [hecoe, hDz]
    exact ((hf z (heU hz)).contDiffAt (hU.mem_nhds (heU hz))).differentiableAt (by simp) |>.hasFDerivAt

theorem exists_smooth_implicit_chart
    (φ : ImplicitFunctionData ℝ E F G) (U : Set E) (hU : IsOpen U)
    (hx : φ.pt ∈ U) (hUs : U ⊆ φ.toOpenPartialHomeomorph.source)
    (hl : ContDiffOn ℝ ∞ φ.leftFun U) (hr : ContDiffOn ℝ ∞ φ.rightFun U) :
    ∃ e : OpenPartialHomeomorph E (F × G),
      φ.pt ∈ e.source ∧ e.source ⊆ U ∧ e.source ⊆ φ.toOpenPartialHomeomorph.source ∧
      (e : E → F × G) = φ.prodFun ∧
      (∀ y ∈ e.target, e.symm y = φ.toOpenPartialHomeomorph.symm y) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let D : E ≃L[ℝ] F × G :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hD : HasFDerivAt φ.toOpenPartialHomeomorph (D : E →L[ℝ] F × G) φ.pt := by
    simpa [D, ImplicitFunctionData.toOpenPartialHomeomorph_coe] using φ.hasStrictFDerivAt.hasFDerivAt
  have hf : ContDiffOn ℝ ∞ φ.toOpenPartialHomeomorph U := by
    simpa [ImplicitFunctionData.toOpenPartialHomeomorph_coe, ImplicitFunctionData.prodFun] using hl.prodMk hr
  simpa only [ImplicitFunctionData.toOpenPartialHomeomorph_coe] using
    exists_smooth_neighborhood_restriction φ.toOpenPartialHomeomorph U hU φ.pt hx hUs hf D hD

-- Actual consumer: the produced chart's smooth inverse feeds projected slices.
theorem exists_smooth_chart_with_residual_slices
    {H S : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    (φ : ImplicitFunctionData ℝ E F G) (U : Set E) (hU : IsOpen U)
    (hx : φ.pt ∈ U) (hUs : U ⊆ φ.toOpenPartialHomeomorph.source)
    (hl : ContDiffOn ℝ ∞ φ.leftFun U) (hr : ContDiffOn ℝ ∞ φ.rightFun U)
    (f : E → H) (hf : ContDiffOn ℝ ∞ f U) (Q : H →L[ℝ] S) :
    ∃ e : OpenPartialHomeomorph E (F × G), φ.pt ∈ e.source ∧ e.source ⊆ U ∧
      ∀ r z, z ∈ {z | (r,z) ∈ e.target} →
        ContDiffAt ℝ ∞ (fun w : G => Q (f (e.symm (r,w)))) z := by
  obtain ⟨e, he, hUe, _, _, _, _, hinv⟩ := exists_smooth_implicit_chart φ U hU hx hUs hl hr
  exact ⟨e, he, hUe,
    SardProjectedChartResidualSlicesContDiffOnProbe.contDiffAt_residual_inverseSlices_of_contDiffOn
      e f Q ∞ hinv (hf.mono hUe)⟩

#print axioms exists_smooth_neighborhood_restriction
#print axioms exists_smooth_implicit_chart
#print axioms exists_smooth_chart_with_residual_slices
end SardSmoothNeighborhoodImplicitChartProbe

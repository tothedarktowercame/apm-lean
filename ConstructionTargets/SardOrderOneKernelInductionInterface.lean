import ConstructionTargets.SardFirstNonzeroJetOneFDerivNonzero
import ConstructionTargets.SardProjectedRangeKernelDimensionDrop

open Set MeasureTheory

noncomputable section
namespace SardOrderOneKernelInductionInterfaceProbe

theorem orderOne_kernel_interface_of_lower_dimension
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (K : Set E) (x : E)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1)
    [MeasurableSpace (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ]
    (μS : Measure (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ)
    (g : ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
        (fderiv ℝ f x)).ker →
        (LinearMap.range (fderiv ℝ f x).toLinearMap)ᗮ)
    (s : Set ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
        (fderiv ℝ f x)).ker)
    (hLower : Module.finrank ℝ
        ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
          (fderiv ℝ f x)).ker < Module.finrank ℝ E →
      (∀ y ∈ s, ContDiffAt ℝ 1 g y) →
      μS (g '' (s ∩ {y | ¬ Function.Surjective (fderiv ℝ g y)})) = 0)
    (hg : ∀ y ∈ s, ContDiffAt ℝ 1 g y) :
    μS (g '' (s ∩ {y | ¬ Function.Surjective (fderiv ℝ g y)})) = 0 := by
  apply hLower
  · apply SardProjectedRangeKernelDimensionDropProbe.finrank_ker_rangeProjection_comp_lt
    exact SardFirstNonzeroJetOneFDerivNonzeroProbe.fderiv_ne_zero_of_mem_firstNonzeroJetLocus_one
      f K x hx
  · exact hg

#print axioms orderOne_kernel_interface_of_lower_dimension

end SardOrderOneKernelInductionInterfaceProbe

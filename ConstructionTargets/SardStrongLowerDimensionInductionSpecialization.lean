import ConstructionTargets.SardOrderOneKernelInductionInterface
import ConstructionTargets.SardSmoothCriticalImageInductionAssembly

open Set MeasureTheory

noncomputable section
namespace SardStrongLowerDimensionInductionSpecializationProbe

universe u v

theorem smooth_criticalImage_zero_of_strong_lower_dimension
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    [SecondCountableTopology E] [SigmaCompactSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μF : Measure F) [μF.IsAddHaarMeasure]
    (f : E → F) (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f)
    (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hcritical : ∀ K : Set E,
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ⊆
        criticalSet (fun x => (fderiv ℝ f x).toLinearMap))
    (hLower : ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [FiniteDimensional ℝ G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (T : Type v) [NormedAddCommGroup T] [NormedSpace ℝ T]
        [FiniteDimensional ℝ T] [MeasurableSpace T],
        ∀ (μT : Measure T), Measure.IsAddHaarMeasure μT →
        ∀ (q : WithTop ℕ∞), q ≠ 0 → q ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞) →
        ∀ (g : G → T) (s : Set G),
          (∀ y ∈ s, ContDiffAt ℝ q g y) →
          μT (g '' (s ∩ {y | ¬ Function.Surjective (fderiv ℝ g y)})) = 0) :
    μF (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  apply SardSmoothCriticalImageInductionAssemblyProbe.smooth_criticalImage_zero_of_induction_interfaces
    μF f hf n hn hnTop hcritical
  · intro K x hx μS hμS g s hg
    apply SardOrderOneKernelInductionInterfaceProbe.orderOne_kernel_interface_of_lower_dimension
      f K x hx μS g s
    · intro hdim hreg
      exact hLower _ hdim _ μS hμS 1 (by norm_num) (by norm_num) g s hreg
    · exact hg
  · intro G _ _ _ _ hdim g s hg
    exact hLower G hdim F μF inferInstance n hn hnTop g s hg

#print axioms smooth_criticalImage_zero_of_strong_lower_dimension

end SardStrongLowerDimensionInductionSpecializationProbe

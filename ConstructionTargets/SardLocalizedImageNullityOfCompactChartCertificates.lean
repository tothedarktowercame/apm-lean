import ConstructionTargets.SardFirstDerivativeLocusCompactProjectedChartAggregation
import ConstructionTargets.SardFirstNonzeroJetFiniteAssembly

open Set MeasureTheory

namespace SardLocalizedImageNullityOfCompactChartCertificatesProbe

/-- Taylor-flat and higher-locus nullity together with indexed compact chart
certificates for the order-one locus give nullity of the localized image. -/
theorem image_null_of_flat_higher_and_compactChart_certificates
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (k : ℕ) (hf : ContDiff ℝ 1 f)
    (hflat : μ (f '' SardHigherJetLocusDecompositionProbe.flatThrough f K k) = 0)
    (hhigher : ∀ i ∈ Set.Icc 2 k,
      μ (f '' SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
        f K i) = 0)
    (hcritical :
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ⊆
        criticalSet (fun x => (fderiv ℝ f x).toLinearMap))
    (hcompact : ∀ r : Fin (Module.finrank ℝ F), ∀ x, x ∈
      SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus f K 1 ∩
        rankStratum (fun y => (fderiv ℝ f y).toLinearMap) r →
      ∀ chart : OpenPartialHomeomorph E
          ((LinearMap.range (fderiv ℝ f x).toLinearMap) ×
            ((LinearMap.range (fderiv ℝ f x).toLinearMap).orthogonalProjection.comp
              (fderiv ℝ f x)).ker),
      ∀ V : Set E, IsOpen V → x ∈ V → V ⊆ chart.source →
        ∀ C : Set E, IsCompact C →
          C ⊆ {y | Module.finrank ℝ
            (LinearMap.range (fderiv ℝ f y).toLinearMap) ≤ r} ∩ V →
          μ (f '' C) = 0) :
    μ (f '' K) = 0 := by
  apply SardFirstNonzeroJetFiniteAssemblyProbe.image_null_of_flat_first_and_higher_firstNonzeroJetLoci
    μ f K k hflat
  · exact SardFirstDerivativeLocusCompactProjectedChartAggregationProbe.firstNonzeroJetLocus_one_image_null_of_compact_projectedChart_certificates
      μ f K hf hcritical hcompact
  · exact hhigher

#print axioms image_null_of_flat_higher_and_compactChart_certificates

end SardLocalizedImageNullityOfCompactChartCertificatesProbe

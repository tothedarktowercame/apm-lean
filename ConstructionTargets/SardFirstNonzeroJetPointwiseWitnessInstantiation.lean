import ConstructionTargets.SardFirstNonzeroJetOpenRegularityData
import ConstructionTargets.SardFirstNonzeroJetPointwiseLocalNullityWitness

open Set MeasureTheory

noncomputable section
namespace SardFirstNonzeroJetPointwiseWitnessInstantiationProbe

universe u v

/-- Global smoothness and a lower-dimensional local Sard hypothesis instantiate
the scalarized chart package into a pointwise null-image neighborhood. -/
theorem exists_open_local_image_null_of_firstNonzeroJet
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (f : E → F) (K : Set E) (i : ℕ) (hi : 1 ≤ i)
    (n : WithTop ℕ∞) (hn : n ≠ 0)
    (hnTop : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hf1 : ContDiff ℝ (i + 1) f) (hfn : ContDiff ℝ (n + i) f)
    (hind : ∀ (G : Type u) [NormedAddCommGroup G] [NormedSpace ℝ G]
      [FiniteDimensional ℝ G] [CompleteSpace G],
      Module.finrank ℝ G < Module.finrank ℝ E →
      ∀ (q : G → F) (u : Set G),
        (∀ z ∈ u, ContDiffAt ℝ n q z) →
        μ (q '' (u ∩ {z | ¬ Function.Surjective (fderiv ℝ q z)})) = 0)
    (hKcrit : ∀ y ∈ K, ¬ Function.Surjective (fderiv ℝ f y))
    (x : E)
    (hx : x ∈ SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
      f K (i + 1)) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      μ (f '' (SardFirstNonzeroJetLocusDecompositionProbe.firstNonzeroJetLocus
        f K (i + 1) ∩ U)) = 0 := by
  obtain ⟨h, v, ℓ, _hne, φ, hleft, _hderiv, hpt, hdim, _hcont,
      V, hVopen, hVmem, hVreg⟩ :=
    SardFirstNonzeroJetOpenRegularityDataProbe.exists_scalarizedJet_openRegularityData
      f i n x hf1 hfn hn hnTop hx.2.2
  let g := fun y => ℓ (iteratedFDeriv ℝ i f y v)
  let L := fderiv ℝ g x
  let G := (L : E →ₗ[ℝ] ℝ).ker
  letI hG : CompleteSpace G :=
    SardScalarizedJetImplicitFunctionDataProbe.kernelCompleteSpace L
  have hindG := @hind G inferInstance inferInstance inferInstance hG
  apply @SardFirstNonzeroJetPointwiseLocalNullityWitnessProbe.exists_open_firstNonzeroJetLocus_local_image_null
    E F G inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hG
    μ n hindG φ f K i hi v ℓ x hleft hpt hx V hVopen hVmem hdim hn
  · intro z hz
    exact (hfn.of_le (le_add_right le_rfl)).contDiffAt
  · intro z hz
    exact (hVreg z hz.2).1
  · exact hKcrit

#print axioms exists_open_local_image_null_of_firstNonzeroJet
end SardFirstNonzeroJetPointwiseWitnessInstantiationProbe

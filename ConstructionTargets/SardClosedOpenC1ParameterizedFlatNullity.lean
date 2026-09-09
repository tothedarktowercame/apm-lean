import ConstructionTargets.SardCompactLipschitzParameterizedFlatNullity
import ConstructionTargets.SardClosedOpenImageNullity

open Set MeasureTheory

theorem closed_inter_open_C1_parameterized_flat_image_addHaar_eq_zero
    {G E F : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [Nontrivial G] [MeasurableSpace G] [BorelSpace G]
    [ProperSpace G] [SecondCountableTopology G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (p : G → E) (s U : Set G)
    (hs : IsClosed s) (hU : IsOpen U) (k : ℕ)
    (hp : ∀ a ∈ U, ContDiffAt ℝ 1 p a)
    (hf : ContDiff ℝ (k + 1) f)
    (hflat : ∀ a ∈ s ∩ U, ∀ i, 1 ≤ i → i ≤ k →
      iteratedFDeriv ℝ i f (p a) = 0)
    (hdim : Module.finrank ℝ G < (k + 1) * Module.finrank ℝ F) :
    μ ((f ∘ p) '' (s ∩ U)) = 0 := by
  apply SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open
    μ (f ∘ p) s U hs hU
  intro K hK hsub
  have hlocal : LocallyLipschitzOn K p := by
    intro a ha
    obtain ⟨L, V, hV, hLip⟩ := (hp a (hsub ha).2).exists_lipschitzOnWith
    exact ⟨L, V, mem_nhdsWithin_of_mem_nhds hV, hLip⟩
  obtain ⟨L, hL⟩ := hlocal.exists_lipschitzOnWith_of_compact hK
  exact compact_lipschitz_parameterized_flat_image_addHaar_eq_zero
    μ f p K hK k L hL hf (fun a ha => hflat a (hsub ha)) hdim

#print axioms closed_inter_open_C1_parameterized_flat_image_addHaar_eq_zero

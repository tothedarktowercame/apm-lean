import ConstructionTargets.SardClosedOpenC1ParameterizedFlatNullity

open Set MeasureTheory

theorem C1_parameterized_flat_locus_image_addHaar_eq_zero
    {G E F : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [Nontrivial G] [MeasurableSpace G] [BorelSpace G]
    [ProperSpace G] [SecondCountableTopology G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (p : G → E) (U : Set G) (hU : IsOpen U) (k : ℕ)
    (hp : ∀ a ∈ U, ContDiffAt ℝ 1 p a)
    (hf : ContDiff ℝ (k + 1) f)
    (hdim : Module.finrank ℝ G < (k + 1) * Module.finrank ℝ F) :
    μ ((f ∘ p) '' {a ∈ U | ∀ i, 1 ≤ i → i ≤ k →
      iteratedFDeriv ℝ i f (p a) = 0}) = 0 := by
  let Z : Set E := {x | ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0}
  have hZ : IsClosed Z := by
    rw [show Z = ⋂ i : ℕ, if 1 ≤ i ∧ i ≤ k
        then {x | iteratedFDeriv ℝ i f x = 0} else Set.univ by
      ext x
      simp [Z]]
    apply isClosed_iInter
    intro i
    split_ifs with hi
    · exact isClosed_eq (hf.continuous_iteratedFDeriv (by exact_mod_cast (show i ≤ k + 1 by omega)))
        continuous_const
    · exact isClosed_univ
  have hpc : ContinuousOn p U := fun a ha => (hp a ha).continuousAt.continuousWithinAt
  obtain ⟨s, hs, heq⟩ := continuousOn_iff_isClosed.mp hpc Z hZ
  have hlocus : {a ∈ U | ∀ i, 1 ≤ i → i ≤ k →
      iteratedFDeriv ℝ i f (p a) = 0} = s ∩ U := by
    rw [← heq]
    ext a
    simp [Z, and_comm]
  rw [hlocus]
  apply closed_inter_open_C1_parameterized_flat_image_addHaar_eq_zero
    μ f p s U hs hU k hp hf
  · intro a ha
    have ham : a ∈ p ⁻¹' Z ∩ U := by rw [heq]; exact ha
    exact ham.1
  · exact hdim

#print axioms C1_parameterized_flat_locus_image_addHaar_eq_zero

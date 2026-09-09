import ConstructionTargets.SardFiniteOrderRankZeroSameSpaceEndpointNullity

open Set MeasureTheory

theorem sameSpace_ambient_criticalImage_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → E) (s : Set E)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    μ (f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun x => fderiv ℝ f x)
  · intro x hx
    exact (hf x hx.1).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    by_contra hn
    apply hx.2
    intro y
    obtain ⟨z, hz⟩ := (LinearMap.equivOfIsUnitDet
      (f := (fderiv ℝ f x).toLinearMap) (isUnit_iff_ne_zero.mpr hn)).surjective y
    exact ⟨z, by simpa only [LinearMap.equivOfIsUnitDet_apply] using hz⟩

#print axioms sameSpace_ambient_criticalImage_zero

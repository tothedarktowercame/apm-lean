import ConstructionTargets.SardLowerDimensionSurjectiveLiftNullity

open Set MeasureTheory

theorem lowerDimension_ambient_image_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (f : E → F) (s : Set E)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    μ (f '' s) = 0 := by
  classical
  let e := (Module.finBasis ℝ E).equivFun
  let g := (Module.finBasis ℝ F).equivFun
  let q : (Fin (Module.finrank ℝ F) → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ E) → ℝ) :=
    { toFun := fun v i => v ⟨i.val, lt_trans i.isLt hdim⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hq : Function.Surjective q := by
    intro v
    refine ⟨fun j => if h : j.val < Module.finrank ℝ E then v ⟨j.val, h⟩ else 0, ?_⟩
    funext i
    simp [q, i.isLt]
  let p : F →ₗ[ℝ] E := e.symm.toLinearMap.comp (q.comp g.toLinearMap)
  have hp : Function.Surjective p := e.symm.surjective.comp (hq.comp g.surjective)
  exact image_zero_of_lower_dimension_surjective_lift μ
    (LinearMap.toContinuousLinearMap p) hp f s hdim hf

#print axioms lowerDimension_ambient_image_zero

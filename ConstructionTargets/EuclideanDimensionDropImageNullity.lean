import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Null images from an explicit positive-dimensional complement -/

open Set MeasureTheory
noncomputable section

namespace ConstructionTargets.EuclideanDimensionDropImageNullity

variable {E G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]
  [Nontrivial G]

/-- Extending `f : E → E × G` constantly in the complementary `G`
direction produces a square-dimensional map with the same range. -/
def complementExtension (f : E → E × G) : E × G → E × G :=
  fun x ↦ f x.1

/-- The complement extension has exactly the same range as the original map. -/
theorem range_complementExtension (f : E → E × G) :
    range (complementExtension f) = range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(x, 0), rfl⟩

/-- Every derivative of the complement extension is singular: it kills a
nonzero vector in the complementary factor. -/
theorem det_complementExtensionDerivative_eq_zero
    (f' : E →L[ℝ] E × G) :
    (f'.comp (ContinuousLinearMap.fst ℝ E G)).det = 0 := by
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
  obtain ⟨g, hg⟩ := exists_ne (0 : G)
  intro hker
  have hmem : ((0 : E), g) ∈
      LinearMap.ker (f'.comp (ContinuousLinearMap.fst ℝ E G)).toLinearMap := by
    simp
  rw [hker] at hmem
  exact hg (by simpa using congrArg Prod.snd hmem)

/-- A differentiable map into a finite-dimensional target with an explicit
nontrivial complementary factor has add-Haar-null range. -/
theorem addHaar_range_eq_zero_of_differentiable
    (f : E → E × G) (hf : Differentiable ℝ f)
    (μ : Measure (E × G)) [μ.IsAddHaarMeasure] :
    μ (range f) = 0 := by
  let p : E × G →L[ℝ] E := ContinuousLinearMap.fst ℝ E G
  let g := complementExtension f
  let g' : E × G → (E × G →L[ℝ] E × G) :=
    fun x ↦ (fderiv ℝ f x.1).comp p
  have hg' : ∀ x, HasFDerivAt g (g' x) x := by
    intro x
    exact (hf x.1).hasFDerivAt.comp x hasFDerivAt_fst
  have hdet : ∀ x, (g' x).det = 0 := by
    intro x
    exact det_complementExtensionDerivative_eq_zero (fderiv ℝ f x.1)
  have hnull := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ := μ) (s := (Set.univ : Set (E × G)))
    (f := g) (f' := g')
    (fun x _ ↦ (hg' x).hasFDerivWithinAt) (fun x _ ↦ hdet x)
  simpa [image_univ, g, range_complementExtension] using hnull

/-- Arbitrary subsets of the lower-dimensional source also have null image. -/
theorem addHaar_image_eq_zero_of_differentiable
    (f : E → E × G) (hf : Differentiable ℝ f)
    (μ : Measure (E × G)) [μ.IsAddHaarMeasure]
    (s : Set E) :
    μ (f '' s) = 0 := by
  exact measure_mono_null (image_subset_range f s)
    (addHaar_range_eq_zero_of_differentiable f hf μ)

#print axioms range_complementExtension
#print axioms det_complementExtensionDerivative_eq_zero
#print axioms addHaar_range_eq_zero_of_differentiable
#print axioms addHaar_image_eq_zero_of_differentiable

end ConstructionTargets.EuclideanDimensionDropImageNullity

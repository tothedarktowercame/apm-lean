import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.LinearAlgebra.Dimension.Constructions

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

section EquivTransport

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Nullity transports through an explicit continuous linear splitting of the
target into the source and a nontrivial complementary factor. -/
theorem addHaar_range_eq_zero_of_equiv
    (e : F ≃L[ℝ] E × G) (f : E → F) (hf : Differentiable ℝ f)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (range f) = 0 := by
  let ν : Measure (E × G) := Measure.map e μ
  letI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  have hef : Differentiable ℝ (fun x ↦ e (f x)) := by
    intro x
    exact (e.toContinuousLinearMap.hasFDerivAt.comp x
      (hf x).hasFDerivAt).differentiableAt
  have hnull : ν (range fun x ↦ e (f x)) = 0 :=
    addHaar_range_eq_zero_of_differentiable (fun x ↦ e (f x)) hef ν
  have hpre := Measure.preimage_null_of_map_null
    e.continuous.measurable.aemeasurable hnull
  have hrange : e ⁻¹' (range fun x ↦ e (f x)) = range f := by
    ext x
    simp
  rw [hrange] at hpre
  exact hpre

/-- Subset form of `addHaar_range_eq_zero_of_equiv`. -/
theorem addHaar_image_eq_zero_of_equiv
    (e : F ≃L[ℝ] E × G) (f : E → F) (hf : Differentiable ℝ f)
    (μ : Measure F) [μ.IsAddHaarMeasure] (s : Set E) :
    μ (f '' s) = 0 := by
  exact measure_mono_null (image_subset_range f s)
    (addHaar_range_eq_zero_of_equiv e f hf μ)

/-- Strictly lower finite real dimension implies null range. The complement is
constructed as a finite coordinate space of dimension
`finrank F - finrank E`; no complement is assumed. -/
theorem addHaar_range_eq_zero_of_finrank_lt
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : E → F) (hf : Differentiable ℝ f)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (range f) = 0 := by
  let d := Module.finrank ℝ F - Module.finrank ℝ E
  have hd : 0 < d := Nat.sub_pos_of_lt hdim
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let e : F ≃L[ℝ] E × (Fin d → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simp only [Module.finrank_prod]
      have hfin : Module.finrank ℝ (Fin d → ℝ) = d := by simp
      rw [hfin]
      omega)
  exact addHaar_range_eq_zero_of_equiv e f hf μ

/-- Arbitrary-subset form of the strict-finrank image-nullity theorem. -/
theorem addHaar_image_eq_zero_of_finrank_lt
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (f : E → F) (hf : Differentiable ℝ f)
    (μ : Measure F) [μ.IsAddHaarMeasure] (s : Set E) :
    μ (f '' s) = 0 := by
  exact measure_mono_null (image_subset_range f s)
    (addHaar_range_eq_zero_of_finrank_lt hdim f hf μ)

end EquivTransport

#print axioms range_complementExtension
#print axioms det_complementExtensionDerivative_eq_zero
#print axioms addHaar_range_eq_zero_of_differentiable
#print axioms addHaar_image_eq_zero_of_differentiable
#print axioms addHaar_range_eq_zero_of_equiv
#print axioms addHaar_image_eq_zero_of_equiv
#print axioms addHaar_range_eq_zero_of_finrank_lt
#print axioms addHaar_image_eq_zero_of_finrank_lt

end ConstructionTargets.EuclideanDimensionDropImageNullity

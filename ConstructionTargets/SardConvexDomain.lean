import ConstructionTargets.SardGeneralModel

open scoped ContDiff Manifold
open Set MeasureTheory

noncomputable section

theorem ContDiffWithinAt.domDomCongr_iteratedFDerivWithin_two_of_infty
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {x : E}
    (hf : ContDiffWithinAt ℝ ∞ f s x) (hu : UniqueDiffOn ℝ s)
    (hxs : x ∈ s) (hxi : x ∈ closure (interior s)) :
    (iteratedFDerivWithin ℝ 2 f s x).domDomCongr Fin.revPerm =
      iteratedFDerivWithin ℝ 2 f s x := by
  rw [← isSymmSndFDerivWithinAt_iff_iteratedFDerivWithin hu hxs]
  apply hf.isSymmSndFDerivWithinAt
  · rw [minSmoothness_of_isRCLikeNormedField]
    exact (show (2 : WithTop ENat) ≤ ((⊤ : ENat) : WithTop ENat) from
      WithTop.coe_le_coe.mpr le_top)
  · exact hu
  · exact hxi
  · exact hxs

namespace ConstructionTargets.SardConvexDomain

theorem modelRange_withinCriticalImage_subset_interior_union_frontier
    {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : ModelWithCorners ℝ E H) (f : E → F) :
    f '' {x | x ∈ Set.range I ∧
      ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)} ⊆
      f '' {x | x ∈ interior (Set.range I) ∧
        ¬ Function.Surjective (fderiv ℝ f x)} ∪
      f '' frontier (Set.range I) := by
  rintro y ⟨x, hx, rfl⟩
  by_cases hxi : x ∈ interior (Set.range I)
  · left
    refine ⟨x, ⟨hxi, ?_⟩, rfl⟩
    exact fun hsurj => hx.2
      ((_root_.ConstructionTargets.SardGeneralModel.modelRange_interior_surjective_fderivWithin_iff
        I f x hxi).2 hsurj)
  · right
    refine ⟨x, ?_, rfl⟩
    rw [frontier, I.isClosed_range.closure_eq]
    exact ⟨hx.1, hxi⟩

theorem modelRange_withinCriticalImage_null_of_interior_of_frontier
    {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] (I : ModelWithCorners ℝ E H) (f : E → F)
    (mu : Measure F)
    (hinterior : mu (f '' {x | x ∈ interior (Set.range I) ∧
      ¬ Function.Surjective (fderiv ℝ f x)}) = 0)
    (hfrontier : mu (f '' frontier (Set.range I)) = 0) :
    mu (f '' {x | x ∈ Set.range I ∧
      ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x)}) = 0 := by
  apply measure_mono_null
    (modelRange_withinCriticalImage_subset_interior_union_frontier I f)
  exact measure_union_null hinterior hfrontier

end ConstructionTargets.SardConvexDomain

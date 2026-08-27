import ConstructionTargets.CountableExtendedChartRangeDecomposition
import ConstructionTargets.EuclideanDimensionDropImageNullity
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-! # Transporting countably charted null image patches to one target chart -/

open Set MeasureTheory
noncomputable section

namespace ConstructionTargets.VaryingTargetChartNullityAssembly

open CountableExtendedChartRangeDecomposition

variable {F N : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {H : Type*} [TopologicalSpace H] (J : ModelWithCorners ℝ F H)
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J 1 N]

/-- Nullness in the coordinates of one extended chart. Extended charts are
`PartialEquiv`s, so this is the precise variant applicable to them. -/
def ExtChartCoordinateNull (mu : Measure F) (p : N) (s : Set N) : Prop :=
  s ⊆ (extChartAt J p).source ∧ mu (extChartAt J p '' s) = 0

theorem ExtChartCoordinateNull.mono (mu : Measure F) {p : N} {s t : Set N}
    (hs : ExtChartCoordinateNull J mu p s) (hts : t ⊆ s) :
    ExtChartCoordinateNull J mu p t := by
  exact ⟨fun _ hx ↦ hs.1 (hts hx), measure_mono_null (image_mono hts) hs.2⟩

/-- Transport nullness through the genuine smooth extended-chart overlap. -/
theorem extChartCoordinateNull_inter_source
    (mu : Measure F) [mu.IsAddHaarMeasure]
    (p q : N) (s : Set N) (hs : ExtChartCoordinateNull J mu p s) :
    ExtChartCoordinateNull J mu q (s ∩ (extChartAt J q).source) := by
  let t := s ∩ (extChartAt J q).source
  have ht : ExtChartCoordinateNull J mu p t := hs.mono J mu inter_subset_left
  have hsub : extChartAt J p '' t ⊆
      ((extChartAt J p).symm.trans (extChartAt J q)).source := by
    rintro z ⟨x, hx, rfl⟩
    constructor
    · exact (extChartAt J p).map_source (ht.1 hx)
    · change (extChartAt J p).symm (extChartAt J p x) ∈ (extChartAt J q).source
      rw [(extChartAt J p).left_inv (ht.1 hx)]
      exact hx.2
  have hdiff : DifferentiableOn ℝ
      (extChartAt J q ∘ (extChartAt J p).symm) (extChartAt J p '' t) :=
    ((contDiffOn_ext_coord_change (n := 1) q p).differentiableOn one_ne_zero).mono hsub
  have hcoord : ∀ x ∈ t,
      (extChartAt J q ∘ (extChartAt J p).symm) (extChartAt J p x) = extChartAt J q x := by
    intro x hx
    simp only [Function.comp_apply]
    rw [(extChartAt J p).left_inv (ht.1 hx)]
  have himage :
      (extChartAt J q ∘ (extChartAt J p).symm) '' (extChartAt J p '' t) =
        extChartAt J q '' t := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hcoord x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨extChartAt J p x, ⟨x, hx, rfl⟩, hcoord x hx⟩
  refine ⟨inter_subset_right, ?_⟩
  rw [← himage]
  exact
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero mu hdiff ht.2

/-- Assemble varying-chart null patches in one explicitly fixed target chart. -/
theorem fixed_extChartAt_null_of_countable_patch_decomposition
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {ι : Type*} [Countable ι] (center : ι → N) (piece : ι → Set N)
    (r : Set N) (hr : r = ⋃ i, piece i)
    (hnull : ∀ i, ExtChartCoordinateNull J mu (center i) (piece i)) (q : N) :
    ExtChartCoordinateNull J mu q (r ∩ (extChartAt J q).source) := by
  have hinter : r ∩ (extChartAt J q).source =
      ⋃ i, piece i ∩ (extChartAt J q).source := by
    rw [hr, iUnion_inter]
  rw [hinter]
  constructor
  · rintro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact (extChartCoordinateNull_inter_source J mu (center i) q (piece i) (hnull i)).1 hxi
  · rw [image_iUnion]
    exact measure_iUnion_null fun i ↦
      (extChartCoordinateNull_inter_source J mu (center i) q (piece i) (hnull i)).2

/-- Set-indexed form matching the centers returned by
`exists_countable_chartPairPatch_range_decomposition`.  The displayed
double-union equation is converted explicitly to a union over the countable
subtype of chosen centers. -/
theorem fixed_extChartAt_null_of_countable_centers
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {α : Type*} (centers : Set α) (hcenters : centers.Countable)
    (center : α → N) (piece : α → Set N) (r : Set N)
    (hr : r = ⋃ x ∈ centers, piece x)
    (hnull : ∀ x ∈ centers, ExtChartCoordinateNull J mu (center x) (piece x))
    (q : N) : ExtChartCoordinateNull J mu q (r ∩ (extChartAt J q).source) := by
  letI : Countable centers := hcenters.to_subtype
  have hr' : r = ⋃ x : centers, piece x.1 := by
    rw [hr]
    ext y
    simp only [mem_iUnion, Subtype.exists]
  exact fixed_extChartAt_null_of_countable_patch_decomposition J mu
    (fun x : centers ↦ center x.1) (fun x : centers ↦ piece x.1) r hr'
    (fun x ↦ hnull x.1 x.2) q

/-- Direct consumer for the range decomposition supplied by
`CountableExtendedChartRangeDecomposition`: only the local nullity of each
literal chart-pair image patch remains to be supplied. -/
theorem fixed_extChartAt_null_of_chartPairPatch_range
    (mu : Measure F) [mu.IsAddHaarMeasure]
    {E M H₀ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H₀] (I : ModelWithCorners ℝ E H₀)
    [TopologicalSpace M] [ChartedSpace H₀ M] [IsManifold I 1 M]
    (f : M → N) (centers : Set M) (hcenters : centers.Countable)
    (hrange : range f = ⋃ x ∈ centers, f '' chartPairPatch I J f x)
    (hnull : ∀ x ∈ centers,
      ExtChartCoordinateNull J mu (f x) (f '' chartPairPatch I J f x))
    (q : N) :
    ExtChartCoordinateNull J mu q (range f ∩ (extChartAt J q).source) := by
  exact fixed_extChartAt_null_of_countable_centers J mu centers hcenters f
    (fun x ↦ f '' chartPairPatch I J f x) (range f) hrange hnull q

#print axioms ExtChartCoordinateNull.mono
#print axioms extChartCoordinateNull_inter_source
#print axioms fixed_extChartAt_null_of_countable_patch_decomposition
#print axioms fixed_extChartAt_null_of_countable_centers
#print axioms fixed_extChartAt_null_of_chartPairPatch_range

end ConstructionTargets.VaryingTargetChartNullityAssembly

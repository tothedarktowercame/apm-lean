import ConstructionTargets.EuclideanDimensionDropImageNullity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! # Strict dimension drop in one chosen target chart -/

open Set MeasureTheory
noncomputable section

namespace ConstructionTargets.ChartCoordinateDimensionDropNullity

variable {M E F : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Nullness stated only in one explicit manifold chart.  This does not put a
measure on `M`. -/
def ChartCoordinateNull (μ : Measure F) (φ : OpenPartialHomeomorph M F)
    (s : Set M) : Prop :=
  s ⊆ φ.source ∧ μ (φ '' s) = 0

/-- A differentiable strict-dimension-drop coordinate map has null image in
the chosen target chart.  `hcoord` is the exact chart equation on the source
patch; no global chart cover is used. -/
theorem chartCoordinateNull_image_of_finrank_lt
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (φ : OpenPartialHomeomorph M F)
    (f : E → F) (hf : Differentiable ℝ f)
    (g : E → M) (s : Set E)
    (hdim : Module.finrank ℝ E < Module.finrank ℝ F)
    (hsource : ∀ x ∈ s, g x ∈ φ.source)
    (hcoord : ∀ x ∈ s, φ (g x) = f x) :
    ChartCoordinateNull μ φ (g '' s) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact hsource x hx
  · have himage : φ '' (g '' s) = f '' s := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, (hcoord x hx).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨g x, ⟨x, hx, rfl⟩, hcoord x hx⟩
    rw [himage]
    exact
      EuclideanDimensionDropImageNullity.addHaar_image_eq_zero_of_finrank_lt
        hdim f hf μ s

/-- Countably many null pieces in one fixed chart have null union in that
same chart. -/
theorem chartCoordinateNull_iUnion
    (μ : Measure F) (φ : OpenPartialHomeomorph M F)
    {ι : Type*} [Countable ι] (s : ι → Set M)
    (hs : ∀ i, ChartCoordinateNull μ φ (s i)) :
    ChartCoordinateNull μ φ (⋃ i, s i) := by
  constructor
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact (hs i).1 hxi
  · rw [image_iUnion]
    exact measure_iUnion_null fun i ↦ (hs i).2

/-- An explicit differentiable overlap map transports coordinate nullness.
The overlap equation and target-chart source containment remain visible. -/
theorem chartCoordinateNull_transport
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (φ ψ : OpenPartialHomeomorph M F) (s : Set M)
    (hsψ : s ⊆ ψ.source)
    (change : F → F) (hchange : DifferentiableOn ℝ change (φ '' s))
    (hcoord : ∀ x ∈ s, change (φ x) = ψ x)
    (hnull : ChartCoordinateNull μ φ s) :
    ChartCoordinateNull μ ψ s := by
  have himage : change '' (φ '' s) = ψ '' s := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hcoord x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ x, ⟨x, hx, rfl⟩, hcoord x hx⟩
  refine ⟨hsψ, ?_⟩
  rw [← himage]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    μ hchange hnull.2

#print axioms chartCoordinateNull_image_of_finrank_lt
#print axioms chartCoordinateNull_iUnion
#print axioms chartCoordinateNull_transport

end ConstructionTargets.ChartCoordinateDimensionDropNullity

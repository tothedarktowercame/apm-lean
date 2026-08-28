import ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A Lebesgue number for a two-open cover of a homotopy square
-/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.HomotopySquareTwoOpenLebesgue

variable {X : Type*} [TopologicalSpace X]
variable {U V : Set X}

/-- The pullbacks of a two-open cover along a continuous square admit one
uniform metric radius on the compact unit square. -/
theorem exists_twoOpen_square_lebesgue_number
    (F : C(unitInterval × unitInterval, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : unitInterval × unitInterval,
      ∃ b : Bool, Metric.ball z δ ⊆ F ⁻¹' twoChart U V b := by
  let cover : Bool → Set (unitInterval × unitInterval) :=
    fun b ↦ F ⁻¹' twoChart U V b
  have hopen : ∀ b, IsOpen (cover b) := by
    intro b
    cases b <;> simp [cover, twoChart, IsOpen.preimage F.continuous, hU, hV]
  have hall : (Set.univ : Set (unitInterval × unitInterval)) ⊆ ⋃ b, cover b := by
    intro z _
    have hz : F z ∈ U ∪ V := by rw [hcover]; trivial
    rcases hz with hzU | hzV
    · exact Set.mem_iUnion.mpr ⟨true, by simpa [cover, twoChart] using hzU⟩
    · exact Set.mem_iUnion.mpr ⟨false, by simpa [cover, twoChart] using hzV⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := Set.univ) isCompact_univ hopen hall
  exact ⟨δ, hδ, fun z ↦ hball z (Set.mem_univ z)⟩

/-- Any subset of the square lying in one Lebesgue ball is carried wholly
into one member of the two-open cover. -/
theorem exists_side_of_set_mem_ball
    (F : C(unitInterval × unitInterval, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (A : Set (unitInterval × unitInterval))
      (z : unitInterval × unitInterval),
      A ⊆ Metric.ball z δ → ∃ b : Bool, F '' A ⊆ twoChart U V b := by
  obtain ⟨δ, hδ, hball⟩ :=
    exists_twoOpen_square_lebesgue_number F hU hV hcover
  refine ⟨δ, hδ, fun A z hAz ↦ ?_⟩
  obtain ⟨b, hb⟩ := hball z
  refine ⟨b, ?_⟩
  rintro _ ⟨w, hwA, rfl⟩
  exact hb (hAz hwA)

/-- Coordinatewise-small rectangles are small for the product max metric,
so each such rectangle is mapped into one cover member. -/
theorem exists_side_of_coordinatewise_small
    (F : C(unitInterval × unitInterval, X))
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (A : Set (unitInterval × unitInterval))
      (z : unitInterval × unitInterval),
      (∀ w ∈ A, dist w.1 z.1 < δ ∧ dist w.2 z.2 < δ) →
      ∃ b : Bool, F '' A ⊆ twoChart U V b := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_side_of_set_mem_ball F hU hV hcover
  refine ⟨δ, hδ, fun A z hcoord ↦ hsmall A z ?_⟩
  intro w hw
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  exact hcoord w hw

/-- Homotopies of paths inherit the same square-cover radius from their
underlying continuous map. -/
theorem Path.Homotopy.exists_twoOpen_lebesgue_number
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : unitInterval × unitInterval,
      ∃ b : Bool, Metric.ball z δ ⊆ H ⁻¹' twoChart U V b :=
  exists_twoOpen_square_lebesgue_number H.toContinuousMap hU hV hcover

#print axioms exists_twoOpen_square_lebesgue_number
#print axioms exists_side_of_set_mem_ball
#print axioms exists_side_of_coordinatewise_small
#print axioms Path.Homotopy.exists_twoOpen_lebesgue_number

end ConstructionTargets.HomotopySquareTwoOpenLebesgue

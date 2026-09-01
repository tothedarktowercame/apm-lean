import ConstructionTargets.PointWedgeQuotient

open Set Topology

noncomputable section

namespace ConstructionTargets.PointWedgeRestrictedOpenQuotient

open ConstructionTargets.PointWedgeQuotient

universe u v

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Representatives whose left and right coordinates lie in the prescribed subsets. -/
def restrictedPreimage (A : Set X) (B : Set Y) : Set (Sum X Y)
  | .inl x => x ∈ A
  | .inr y => y ∈ B

theorem restrictedPreimage_isOpen {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) :
    IsOpen (restrictedPreimage A B) := by
  rw [isOpen_sum_iff]
  exact ⟨hA, hB⟩

/-- The saturated restricted part of a point wedge. -/
def restrictedOpen (x₀ : X) (y₀ : Y) (A : Set X) (B : Set Y) :
    Set (Wedge x₀ y₀) :=
  quotientMap x₀ y₀ '' restrictedPreimage A B

theorem restrictedOpen_isOpen {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    IsOpen (restrictedOpen x₀ y₀ A B) := by
  exact isOpen_image_of_basepoints_mem _ (restrictedPreimage_isOpen hA hB) hx hy

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem quotientMap_preimage_restrictedOpen {x₀ : X} {y₀ : Y}
    {A : Set X} {B : Set Y} (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    quotientMap x₀ y₀ ⁻¹' restrictedOpen x₀ y₀ A B = restrictedPreimage A B := by
  exact preimage_image_of_basepoints_mem _ hx hy

theorem quotientMap_isQuotientMap (x₀ : X) (y₀ : Y) :
    IsQuotientMap (quotientMap x₀ y₀) := by
  exact ⟨surjective_quotientMap x₀ y₀, rfl⟩

/-- The restriction of the wedge quotient map to any open saturated pair of
subspaces is again a quotient map. This is the topology needed to identify
the resulting open subtype with the wedge of the two subtypes. -/
theorem restrictedOpen_quotientMap_isQuotientMap
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    IsQuotientMap
      ((restrictedOpen x₀ y₀ A B).restrictPreimage (quotientMap x₀ y₀)) := by
  apply (quotientMap_isQuotientMap x₀ y₀).restrictPreimage_isOpen
  exact restrictedOpen_isOpen hA hB hx hy

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem restrictedDomain_eq
    {x₀ : X} {y₀ : Y} {A : Set X} {B : Set Y}
    (hx : x₀ ∈ A) (hy : y₀ ∈ B) :
    {a : Sum X Y | quotientMap x₀ y₀ a ∈ restrictedOpen x₀ y₀ A B} =
      restrictedPreimage A B := by
  exact quotientMap_preimage_restrictedOpen hx hy

#print axioms restrictedPreimage_isOpen
#print axioms restrictedOpen_isOpen
#print axioms quotientMap_preimage_restrictedOpen
#print axioms quotientMap_isQuotientMap
#print axioms restrictedOpen_quotientMap_isQuotientMap
#print axioms restrictedDomain_eq

end ConstructionTargets.PointWedgeRestrictedOpenQuotient

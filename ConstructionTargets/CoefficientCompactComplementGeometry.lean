import Mathlib

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementGeometry

open Set

variable {X : Type}

/-- The ambient complement used for compact-support Mayer--Vietoris. -/
def ambient (K L : Set X) : Set X := (K ∩ L)ᶜ

/-- The part of the ambient complement lying outside `K`. -/
def left (K L : Set X) : Set (ambient K L) := Subtype.val ⁻¹' Kᶜ

/-- The part of the ambient complement lying outside `L`. -/
def right (K L : Set X) : Set (ambient K L) := Subtype.val ⁻¹' Lᶜ

theorem left_open [TopologicalSpace X] [T2Space X]
    {K L : Set X} (hK : IsCompact K) : IsOpen (left K L) :=
  hK.isClosed.isOpen_compl.preimage continuous_subtype_val

theorem right_open [TopologicalSpace X] [T2Space X]
    {K L : Set X} (hL : IsCompact L) : IsOpen (right K L) :=
  hL.isClosed.isOpen_compl.preimage continuous_subtype_val

/-- The two actual complement pieces cover the complement of the intersection. -/
theorem left_union_right (K L : Set X) : left K L ∪ right K L = univ := by
  ext x
  simp only [left, right, mem_union, mem_preimage, mem_compl_iff, mem_univ, iff_true]
  exact not_and_or.mp x.property

/-- Their overlap is literally the inverse image of the complement of the union. -/
theorem left_inter_right (K L : Set X) :
    left K L ∩ right K L = Subtype.val ⁻¹' (K ∪ L)ᶜ := by
  ext x
  simp [left, right]

/-- Each left point has its canonical value in the original complement of `K`. -/
def leftToKComplement (K L : Set X) : left K L → (Kᶜ : Set X) :=
  fun x => ⟨x.1.1, x.2⟩

/-- Each right point has its canonical value in the original complement of `L`. -/
def rightToLComplement (K L : Set X) : right K L → (Lᶜ : Set X) :=
  fun x => ⟨x.1.1, x.2⟩

/-- Each overlap point has its canonical value in the complement of `K ∪ L`. -/
def overlapToUnionComplement (K L : Set X) :
    (left K L ∩ right K L : Set (ambient K L)) → ((K ∪ L)ᶜ : Set X) :=
  fun x => ⟨x.1.1, by
    rintro (hk | hl)
    · exact x.2.1 hk
    · exact x.2.2 hl⟩

@[simp] theorem leftToKComplement_value (K L : Set X) (x : left K L) :
    (leftToKComplement K L x : X) = x.1.1 := rfl

@[simp] theorem rightToLComplement_value (K L : Set X) (x : right K L) :
    (rightToLComplement K L x : X) = x.1.1 := rfl

@[simp] theorem overlapToUnionComplement_value (K L : Set X)
    (x : (left K L ∩ right K L : Set (ambient K L))) :
    (overlapToUnionComplement K L x : X) = x.1.1 := rfl

#print axioms left_open
#print axioms right_open
#print axioms left_union_right
#print axioms left_inter_right
#print axioms leftToKComplement_value
#print axioms rightToLComplement_value
#print axioms overlapToUnionComplement_value

end ConstructionTargets.CoefficientCompactComplementGeometry

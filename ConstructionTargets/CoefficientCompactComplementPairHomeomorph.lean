import ConstructionTargets.CoefficientCompactComplementSmallComparison

noncomputable section
namespace ConstructionTargets.CoefficientCompactComplementPairHomeomorph

open Set
open ConstructionTargets.CoefficientCompactComplementGeometry
open ConstructionTargets.CoefficientCompactComplementSmallComparison

variable {X : Type} [TopologicalSpace X]

/-- Flatten the nested left complement subtype to the original complement of `K`. -/
def leftHomeomorph (K L : Set X) : left K L ≃ₜ (Kᶜ : Set X) where
  toFun := leftToKComplement K L
  invFun := fun y => ⟨⟨y.1, by exact fun h => y.2 h.1⟩, y.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    change Continuous (fun x : left K L => (⟨x.1.1, x.2⟩ : (Kᶜ : Set X)))
    fun_prop
  continuous_invFun := by fun_prop

/-- Flatten the nested right complement subtype to the original complement of `L`. -/
def rightHomeomorph (K L : Set X) : right K L ≃ₜ (Lᶜ : Set X) where
  toFun := rightToLComplement K L
  invFun := fun y => ⟨⟨y.1, by exact fun h => y.2 h.2⟩, y.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    change Continuous (fun x : right K L => (⟨x.1.1, x.2⟩ : (Lᶜ : Set X)))
    fun_prop
  continuous_invFun := by fun_prop

/-- Flatten the actual overlap to the complement of `K ∪ L`. -/
def overlapHomeomorph (K L : Set X) :
    (overlap K L : Set (ambient K L)) ≃ₜ ((K ∪ L)ᶜ : Set X) where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun y => ⟨⟨y.1, by
    rintro ⟨hk, hl⟩
    exact y.2 (Or.inl hk)⟩, y.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem leftHomeomorph_value (K L : Set X) (x : (left K L : Set (ambient K L))) :
    ((leftHomeomorph K L x : (Kᶜ : Set X)) : X) = x.1.1 := rfl

@[simp] theorem rightHomeomorph_value (K L : Set X) (x : (right K L : Set (ambient K L))) :
    ((rightHomeomorph K L x : (Lᶜ : Set X)) : X) = x.1.1 := rfl

@[simp] theorem overlapHomeomorph_value (K L : Set X)
    (x : (overlap K L : Set (ambient K L))) :
    ((overlapHomeomorph K L x : ((K ∪ L)ᶜ : Set X)) : X) = x.1.1 := rfl

#print axioms leftHomeomorph
#print axioms rightHomeomorph
#print axioms overlapHomeomorph
#print axioms leftHomeomorph_value
#print axioms rightHomeomorph_value
#print axioms overlapHomeomorph_value

end ConstructionTargets.CoefficientCompactComplementPairHomeomorph

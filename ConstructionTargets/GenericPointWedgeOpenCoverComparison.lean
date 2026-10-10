import ConstructionTargets.PointWedgeRestrictedOpenQuotient
import ConstructionTargets.PointWedgePointedContractionDescent
import ConstructionTargets.TorusCircleWedgeOpenCover

open Set Topology
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.GenericPointWedgeOpenCoverComparison

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointWedgeRestrictedOpenQuotient
open ConstructionTargets.PointWedgePointedContractionDescent
open ConstructionTargets.PointedPuncturedCircleContraction
open ConstructionTargets.TorusCircleWedgeOpenCover

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem genericPointWedgeLeftOpen_eq_restricted :
    leftOpen x₀ y₀ M = restrictedOpen x₀ y₀ Set.univ M := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [leftPreimage, restrictedPreimage] using ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [leftPreimage, restrictedPreimage] using ha, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem genericPointWedgeRightOpen_eq_restricted :
    rightOpen x₀ y₀ N = restrictedOpen x₀ y₀ N Set.univ := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [rightPreimage, restrictedPreimage] using ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [rightPreimage, restrictedPreimage] using ha, rfl⟩

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem genericPointWedgeIntersection_eq_restricted
    (hy : y₀ ∈ M) (hx : x₀ ∈ N) :
    leftOpen x₀ y₀ M ∩ rightOpen x₀ y₀ N = restrictedOpen x₀ y₀ N M := by
  rw [genericPointWedgeLeftOpen_eq_restricted,
    genericPointWedgeRightOpen_eq_restricted]
  apply Set.preimage_injective.mpr (surjective_quotientMap x₀ y₀)
  rw [Set.preimage_inter,
    quotientMap_preimage_restrictedOpen (Set.mem_univ _) hy,
    quotientMap_preimage_restrictedOpen hx (Set.mem_univ _),
    quotientMap_preimage_restrictedOpen hx hy]
  ext a
  cases a with
  | inl x => change (True ∧ x ∈ N ↔ x ∈ N); tauto
  | inr y => change (y ∈ M ∧ True ↔ y ∈ M); tauto

def genericPointWedgeLeftHomotopyEquiv
    (hM : IsOpen M) (hy : y₀ ∈ M)
    (cM : PointedContraction M ⟨y₀, hy⟩) :
    {z // z ∈ leftOpen x₀ y₀ M} ≃ₕ X :=
  (Homeomorph.setCongr
      (genericPointWedgeLeftOpen_eq_restricted x₀ y₀ M)).toHomotopyEquiv |>.trans
    ((restrictedOpenHomeomorphWedge isOpen_univ hM (Set.mem_univ _) hy).trans
      (pointedWedgeHomeomorph (Homeomorph.Set.univ X) (Homeomorph.refl M)
        rfl rfl)).toHomotopyEquiv |>.trans
    (wedgeHomotopyEquivLeft cM)

def genericPointWedgeRightHomotopyEquiv
    (hN : IsOpen N) (hx : x₀ ∈ N)
    (cN : PointedContraction N ⟨x₀, hx⟩) :
    {z // z ∈ rightOpen x₀ y₀ N} ≃ₕ Y :=
  (Homeomorph.setCongr
      (genericPointWedgeRightOpen_eq_restricted x₀ y₀ N)).toHomotopyEquiv |>.trans
    ((restrictedOpenHomeomorphWedge hN isOpen_univ hx (Set.mem_univ _)).trans
      (pointedWedgeHomeomorph (Homeomorph.refl N) (Homeomorph.Set.univ Y)
        rfl rfl)).toHomotopyEquiv |>.trans
    (wedgeHomotopyEquivRight cN)

def genericPointWedgeIntersectionHomotopyEquiv
    (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
    (cM : PointedContraction M ⟨y₀, hy⟩)
    (cN : PointedContraction N ⟨x₀, hx⟩) :
    {z // z ∈ leftOpen x₀ y₀ M ∩ rightOpen x₀ y₀ N} ≃ₕ Unit :=
  (Homeomorph.setCongr
      (genericPointWedgeIntersection_eq_restricted x₀ y₀ M N hy hx)).toHomotopyEquiv |>.trans
    (restrictedOpenHomeomorphWedge hN hM hx hy).toHomotopyEquiv |>.trans
    (wedgeHomotopyEquivLeft cM) |>.trans
    (pointedContractionHomotopyEquivUnit cN)

@[simp] theorem genericPointWedgeLeftHomotopyEquiv_inclusion
    (hM : IsOpen M) (hy : y₀ ∈ M)
    (cM : PointedContraction M ⟨y₀, hy⟩) (x : X) :
    genericPointWedgeLeftHomotopyEquiv x₀ y₀ M hM hy cM
      ⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, trivial, rfl⟩⟩ = x := by
  simp only [genericPointWedgeLeftHomotopyEquiv,
    ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
    Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr
      (genericPointWedgeLeftOpen_eq_restricted x₀ y₀ M))
      ⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, trivial, rfl⟩⟩ =
      ⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, Set.mem_univ x, rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [hz, restrictedOpenHomeomorphWedge_left _ _ _ _ x (Set.mem_univ x),
    pointedWedgeHomeomorph_left]
  rfl

@[simp] theorem genericPointWedgeRightHomotopyEquiv_inclusion
    (hN : IsOpen N) (hx : x₀ ∈ N)
    (cN : PointedContraction N ⟨x₀, hx⟩) (y : Y) :
    genericPointWedgeRightHomotopyEquiv x₀ y₀ N hN hx cN
      ⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, trivial, rfl⟩⟩ = y := by
  simp only [genericPointWedgeRightHomotopyEquiv,
    ContinuousMap.HomotopyEquiv.trans_apply, Homeomorph.coe_toHomotopyEquiv,
    Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr
      (genericPointWedgeRightOpen_eq_restricted x₀ y₀ N))
      ⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, trivial, rfl⟩⟩ =
      ⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, Set.mem_univ y, rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [hz, restrictedOpenHomeomorphWedge_right _ _ _ _ y (Set.mem_univ y),
    pointedWedgeHomeomorph_right]
  rfl

structure GenericPointWedgeCoverPackage
    (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N) where
  leftOpen_isOpen : IsOpen (leftOpen x₀ y₀ M)
  rightOpen_isOpen : IsOpen (rightOpen x₀ y₀ N)
  union_eq_univ : leftOpen x₀ y₀ M ∪ rightOpen x₀ y₀ N = Set.univ
  leftEquiv : {z // z ∈ leftOpen x₀ y₀ M} ≃ₕ X
  rightEquiv : {z // z ∈ rightOpen x₀ y₀ N} ≃ₕ Y
  intersectionEquiv :
    {z // z ∈ leftOpen x₀ y₀ M ∩ rightOpen x₀ y₀ N} ≃ₕ Unit
  left_inclusion : ∀ x : X,
    leftEquiv ⟨quotientMap x₀ y₀ (.inl x), ⟨.inl x, trivial, rfl⟩⟩ = x
  right_inclusion : ∀ y : Y,
    rightEquiv ⟨quotientMap x₀ y₀ (.inr y), ⟨.inr y, trivial, rfl⟩⟩ = y

def genericPointWedgeCoverPackage
    (hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
    (cM : PointedContraction M ⟨y₀, hy⟩)
    (cN : PointedContraction N ⟨x₀, hx⟩) :
    GenericPointWedgeCoverPackage x₀ y₀ M N hM hN hy hx where
  leftOpen_isOpen := leftOpen_isOpen hM hy
  rightOpen_isOpen := rightOpen_isOpen hN hx
  union_eq_univ := leftOpen_union_rightOpen x₀ y₀ M N
  leftEquiv := genericPointWedgeLeftHomotopyEquiv x₀ y₀ M hM hy cM
  rightEquiv := genericPointWedgeRightHomotopyEquiv x₀ y₀ N hN hx cN
  intersectionEquiv :=
    genericPointWedgeIntersectionHomotopyEquiv x₀ y₀ M N hM hN hy hx cM cN
  left_inclusion := genericPointWedgeLeftHomotopyEquiv_inclusion x₀ y₀ M hM hy cM
  right_inclusion := genericPointWedgeRightHomotopyEquiv_inclusion x₀ y₀ N hN hx cN

#print axioms genericPointWedgeLeftOpen_eq_restricted
#print axioms genericPointWedgeRightOpen_eq_restricted
#print axioms genericPointWedgeIntersection_eq_restricted
#print axioms genericPointWedgeLeftHomotopyEquiv
#print axioms genericPointWedgeRightHomotopyEquiv
#print axioms genericPointWedgeIntersectionHomotopyEquiv
#print axioms genericPointWedgeLeftHomotopyEquiv_inclusion
#print axioms genericPointWedgeRightHomotopyEquiv_inclusion
#print axioms genericPointWedgeCoverPackage

end ConstructionTargets.GenericPointWedgeOpenCoverComparison

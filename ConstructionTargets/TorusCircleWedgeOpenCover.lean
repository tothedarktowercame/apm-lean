import ConstructionTargets.PointWedgeRestrictedOpenQuotient
import ConstructionTargets.PointWedgePointedContractionDescent

open Set Topology
open scoped ContinuousMap
noncomputable section

namespace ConstructionTargets.TorusCircleWedgeOpenCover

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.PointWedgeRestrictedOpenQuotient
open ConstructionTargets.PointWedgePointedContractionDescent
open ConstructionTargets.PointedPuncturedCircleContraction

abbrev Torus := Circle × Circle
abbrev GenericWedge := Wedge ((1, 1) : Torus) (1 : Circle)

def M : Set Circle := {z | (z : ℂ) ≠ -1}
def N : Set Torus := {z | (z.1 : ℂ) ≠ -1 ∧ (z.2 : ℂ) ≠ -1}

theorem M_isOpen : IsOpen M := by
  exact isOpen_ne.preimage continuous_subtype_val

theorem N_isOpen : IsOpen N := by
  exact (isOpen_ne.preimage (continuous_subtype_val.comp continuous_fst)).and
    (isOpen_ne.preimage (continuous_subtype_val.comp continuous_snd))

theorem one_mem_M : (1 : Circle) ∈ M := by norm_num [M]
theorem one_one_mem_N : ((1, 1) : Torus) ∈ N := by norm_num [N]

def U : Set GenericWedge := leftOpen ((1, 1) : Torus) (1 : Circle) M
def V : Set GenericWedge := rightOpen ((1, 1) : Torus) (1 : Circle) N

theorem U_isOpen : IsOpen U := leftOpen_isOpen M_isOpen one_mem_M
theorem V_isOpen : IsOpen V := rightOpen_isOpen N_isOpen one_one_mem_N
theorem U_union_V : U ∪ V = Set.univ :=
  leftOpen_union_rightOpen ((1, 1) : Torus) (1 : Circle) M N

theorem U_eq_restricted :
    U = restrictedOpen ((1, 1) : Torus) (1 : Circle) Set.univ M := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [leftPreimage, restrictedPreimage] using ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [leftPreimage, restrictedPreimage] using ha, rfl⟩

theorem V_eq_restricted :
    V = restrictedOpen ((1, 1) : Torus) (1 : Circle) N Set.univ := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [rightPreimage, restrictedPreimage] using ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, by cases a <;> simpa [rightPreimage, restrictedPreimage] using ha, rfl⟩

theorem U_inter_V :
    U ∩ V = restrictedOpen ((1, 1) : Torus) (1 : Circle) N M := by
  rw [U_eq_restricted, V_eq_restricted]
  apply (Set.preimage_injective.mpr
    (surjective_quotientMap ((1, 1) : Torus) (1 : Circle)))
  rw [Set.preimage_inter,
    quotientMap_preimage_restrictedOpen (Set.mem_univ _) one_mem_M,
    quotientMap_preimage_restrictedOpen one_one_mem_N (Set.mem_univ _),
    quotientMap_preimage_restrictedOpen one_one_mem_N one_mem_M]
  ext a
  cases a with
  | inl x => change (True ∧ x ∈ N ↔ x ∈ N); tauto
  | inr y => change (y ∈ M ∧ True ↔ y ∈ M); tauto

universe u₁ v₁ u₂ v₂
variable {X₁ : Type u₁} {Y₁ : Type v₁} [TopologicalSpace X₁] [TopologicalSpace Y₁]
variable {X₂ : Type u₂} {Y₂ : Type v₂} [TopologicalSpace X₂] [TopologicalSpace Y₂]

private theorem wedgeMap_respects (eX : X₁ ≃ₜ X₂) (eY : Y₁ ≃ₜ Y₂)
    {x₀ : X₁} {y₀ : Y₁} {x₀' : X₂} {y₀' : Y₂}
    (hx : eX x₀ = x₀') (hy : eY y₀ = y₀') (a b : Sum X₁ Y₁)
    (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    quotientMap x₀' y₀' (Sum.map eX eY a) =
      quotientMap x₀' y₀' (Sum.map eX eY b) := by
  induction hab with
  | rel a b hab =>
      cases hab
      rw [Sum.map_inl, Sum.map_inr, hx, hy]
      exact Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def pointedWedgeHomeomorph (eX : X₁ ≃ₜ X₂) (eY : Y₁ ≃ₜ Y₂)
    {x₀ : X₁} {y₀ : Y₁} {x₀' : X₂} {y₀' : Y₂}
    (hx : eX x₀ = x₀') (hy : eY y₀ = y₀') :
    Wedge x₀ y₀ ≃ₜ Wedge x₀' y₀' where
  toFun := Quotient.lift (fun a => quotientMap x₀' y₀' (Sum.map eX eY a))
    (wedgeMap_respects eX eY hx hy)
  invFun := Quotient.lift
    (fun a => quotientMap x₀ y₀ (Sum.map eX.symm eY.symm a))
    (wedgeMap_respects eX.symm eY.symm
      (by simpa using congrArg eX.symm hx.symm)
      (by simpa using congrArg eY.symm hy.symm))
  left_inv := by
    rintro ⟨a⟩
    cases a with
    | inl x => exact congrArg (quotientMap x₀ y₀) (by simp)
    | inr y => exact congrArg (quotientMap x₀ y₀) (by simp)
  right_inv := by
    rintro ⟨a⟩
    cases a with
    | inl x => exact congrArg (quotientMap x₀' y₀') (by simp)
    | inr y => exact congrArg (quotientMap x₀' y₀') (by simp)
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact (continuous_quotientMap x₀' y₀').comp
      (eX.continuous.sumMap eY.continuous)
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact (continuous_quotientMap x₀ y₀).comp
      (eX.symm.continuous.sumMap eY.symm.continuous)

@[simp] theorem pointedWedgeHomeomorph_left
    (eX : X₁ ≃ₜ X₂) (eY : Y₁ ≃ₜ Y₂)
    {x₀ : X₁} {y₀ : Y₁} {x₀' : X₂} {y₀' : Y₂}
    (hx : eX x₀ = x₀') (hy : eY y₀ = y₀') (x : X₁) :
    pointedWedgeHomeomorph eX eY hx hy (quotientMap x₀ y₀ (.inl x)) =
      quotientMap x₀' y₀' (.inl (eX x)) := rfl

@[simp] theorem pointedWedgeHomeomorph_right
    (eX : X₁ ≃ₜ X₂) (eY : Y₁ ≃ₜ Y₂)
    {x₀ : X₁} {y₀ : Y₁} {x₀' : X₂} {y₀' : Y₂}
    (hx : eX x₀ = x₀') (hy : eY y₀ = y₀') (y : Y₁) :
    pointedWedgeHomeomorph eX eY hx hy (quotientMap x₀ y₀ (.inr y)) =
      quotientMap x₀' y₀' (.inr (eY y)) := rfl

def MHomeomorph : M ≃ₜ PuncturedCircle := Homeomorph.refl _

def NHomeomorph : N ≃ₜ PuncturedCircle × PuncturedCircle :=
  (Homeomorph.setCongr (by rfl : N = torusPuncturedNeighborhood)).trans
    puncturedTorusHomeomorphNeighborhood.symm

theorem MHomeomorph_base : MHomeomorph ⟨1, one_mem_M⟩ = puncturedCircleBase := rfl
theorem NHomeomorph_base :
    NHomeomorph ⟨(1, 1), one_one_mem_N⟩ =
      (puncturedCircleBase, puncturedCircleBase) := rfl
theorem torusUnivHomeomorph_base :
    Homeomorph.Set.univ Torus ⟨(1, 1), Set.mem_univ _⟩ = ((1, 1) : Torus) := rfl
theorem circleUnivHomeomorph_base :
    Homeomorph.Set.univ Circle ⟨1, Set.mem_univ _⟩ = (1 : Circle) := rfl

def UModel : U ≃ₜ Wedge ((1, 1) : Torus) puncturedCircleBase :=
  (Homeomorph.setCongr U_eq_restricted).trans
    ((restrictedOpenHomeomorphWedge
      (x₀ := ((1, 1) : Torus)) (y₀ := (1 : Circle))
      isOpen_univ M_isOpen (Set.mem_univ _) one_mem_M).trans
      (pointedWedgeHomeomorph (Homeomorph.Set.univ Torus) MHomeomorph
        torusUnivHomeomorph_base
        MHomeomorph_base))

def VModel : V ≃ₜ Wedge
    (puncturedCircleBase, puncturedCircleBase) (1 : Circle) :=
  (Homeomorph.setCongr V_eq_restricted).trans
    ((restrictedOpenHomeomorphWedge
      (x₀ := ((1, 1) : Torus)) (y₀ := (1 : Circle))
      N_isOpen isOpen_univ one_one_mem_N (Set.mem_univ _)).trans
      (pointedWedgeHomeomorph NHomeomorph (Homeomorph.Set.univ Circle)
        NHomeomorph_base circleUnivHomeomorph_base))

def UVModel : {z // z ∈ U ∩ V} ≃ₜ Wedge
    (puncturedCircleBase, puncturedCircleBase) puncturedCircleBase :=
  (Homeomorph.setCongr U_inter_V).trans
    ((restrictedOpenHomeomorphWedge
      (x₀ := ((1, 1) : Torus)) (y₀ := (1 : Circle))
      N_isOpen M_isOpen one_one_mem_N one_mem_M).trans
      (pointedWedgeHomeomorph NHomeomorph MHomeomorph
        NHomeomorph_base MHomeomorph_base))

@[simp] theorem UModel_left (x : Torus) :
    UModel ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
      ⟨.inl x, trivial, rfl⟩⟩ =
      quotientMap ((1, 1) : Torus) puncturedCircleBase (.inl x) := by
  simp only [UModel, Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr U_eq_restricted)
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
        ⟨.inl x, trivial, rfl⟩⟩ =
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
        ⟨.inl x, Set.mem_univ x, rfl⟩⟩ := by apply Subtype.ext; rfl
  rw [hz]
  rw [restrictedOpenHomeomorphWedge_left _ _ _ _ x (Set.mem_univ x)]
  rfl

@[simp] theorem UModel_right (y : Circle) (hy : y ∈ M) :
    UModel ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
      ⟨.inr y, hy, rfl⟩⟩ =
      quotientMap ((1, 1) : Torus) puncturedCircleBase (.inr ⟨y, hy⟩) := by
  simp only [UModel, Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr U_eq_restricted)
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
        ⟨.inr y, hy, rfl⟩⟩ =
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
        ⟨.inr y, hy, rfl⟩⟩ := by apply Subtype.ext; rfl
  rw [hz]
  rw [restrictedOpenHomeomorphWedge_right _ _ _ _ y hy]
  rfl

@[simp] theorem VModel_left (x : Torus) (hx : x ∈ N) :
    VModel ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
      ⟨.inl x, hx, rfl⟩⟩ =
      quotientMap (puncturedCircleBase, puncturedCircleBase) (1 : Circle)
        (.inl (NHomeomorph ⟨x, hx⟩)) := by
  simp only [VModel, Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr V_eq_restricted)
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
        ⟨.inl x, hx, rfl⟩⟩ =
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
        ⟨.inl x, hx, rfl⟩⟩ := by apply Subtype.ext; rfl
  rw [hz]
  rw [restrictedOpenHomeomorphWedge_left _ _ _ _ x hx]
  rfl

@[simp] theorem VModel_right (y : Circle) :
    VModel ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
      ⟨.inr y, trivial, rfl⟩⟩ =
      quotientMap (puncturedCircleBase, puncturedCircleBase) (1 : Circle) (.inr y) := by
  simp only [VModel, Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr V_eq_restricted)
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
        ⟨.inr y, trivial, rfl⟩⟩ =
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
        ⟨.inr y, Set.mem_univ y, rfl⟩⟩ := by apply Subtype.ext; rfl
  rw [hz]
  rw [restrictedOpenHomeomorphWedge_right _ _ _ _ y (Set.mem_univ y)]
  rfl

@[simp] theorem UVModel_left (x : Torus) (hx : x ∈ N) :
    UVModel ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
      ⟨⟨.inl x, trivial, rfl⟩, ⟨.inl x, hx, rfl⟩⟩⟩ =
      quotientMap (puncturedCircleBase, puncturedCircleBase) puncturedCircleBase
        (.inl (NHomeomorph ⟨x, hx⟩)) := by
  simp only [UVModel, Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr U_inter_V)
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
        ⟨⟨.inl x, trivial, rfl⟩, ⟨.inl x, hx, rfl⟩⟩⟩ =
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inl x),
        ⟨.inl x, hx, rfl⟩⟩ := by apply Subtype.ext; rfl
  rw [hz]
  rw [restrictedOpenHomeomorphWedge_left _ _ _ _ x hx]
  rfl

@[simp] theorem UVModel_right (y : Circle) (hy : y ∈ M) :
    UVModel ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
      ⟨⟨.inr y, hy, rfl⟩, ⟨.inr y, trivial, rfl⟩⟩⟩ =
      quotientMap (puncturedCircleBase, puncturedCircleBase) puncturedCircleBase
        (.inr (MHomeomorph ⟨y, hy⟩)) := by
  simp only [UVModel, Homeomorph.trans_apply]
  have hz : (Homeomorph.setCongr U_inter_V)
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
        ⟨⟨.inr y, hy, rfl⟩, ⟨.inr y, trivial, rfl⟩⟩⟩ =
      ⟨quotientMap ((1, 1) : Torus) (1 : Circle) (.inr y),
        ⟨.inr y, hy, rfl⟩⟩ := by apply Subtype.ext; rfl
  rw [hz]
  rw [restrictedOpenHomeomorphWedge_right _ _ _ _ y hy]
  rfl

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ : X} {y₀ : Y}

omit [TopologicalSpace X] [TopologicalSpace Y] in
private theorem swap_respects (a b : Sum X Y)
    (hab : Relation.EqvGen (Rel x₀ y₀) a b) :
    quotientMap y₀ x₀ (Equiv.sumComm X Y a) =
      quotientMap y₀ x₀ (Equiv.sumComm X Y b) := by
  induction hab with
  | rel a b hab =>
      cases hab
      exact Quotient.sound ((Relation.EqvGen.rel _ _ Rel.base).symm)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def wedgeSwap : Wedge x₀ y₀ ≃ₜ Wedge y₀ x₀ where
  toFun := Quotient.lift
    (fun a => quotientMap y₀ x₀ (Equiv.sumComm X Y a)) swap_respects
  invFun := Quotient.lift
    (fun a => quotientMap x₀ y₀ (Equiv.sumComm Y X a)) swap_respects
  left_inv := by rintro ⟨a⟩; cases a <;> rfl
  right_inv := by rintro ⟨a⟩; cases a <;> rfl
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact (continuous_quotientMap y₀ x₀).comp (Homeomorph.sumComm X Y).continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    exact (continuous_quotientMap x₀ y₀).comp (Homeomorph.sumComm Y X).continuous

@[simp] theorem wedgeSwap_left (x : X) :
    wedgeSwap (x₀ := x₀) (y₀ := y₀) (quotientMap x₀ y₀ (.inl x)) =
      quotientMap y₀ x₀ (.inr x) := rfl

@[simp] theorem wedgeSwap_right (y : Y) :
    wedgeSwap (x₀ := x₀) (y₀ := y₀) (quotientMap x₀ y₀ (.inr y)) =
      quotientMap y₀ x₀ (.inl y) := rfl

@[simp] theorem wedgeSwap_base :
    wedgeSwap (x₀ := x₀) (y₀ := y₀) (quotientMap x₀ y₀ (.inl x₀)) =
      quotientMap y₀ x₀ (.inl y₀) := by
  rw [wedgeSwap_left]
  exact Quotient.sound ((Relation.EqvGen.rel _ _ Rel.base).symm)

def wedgeHomotopyEquivRight
    (h : PointedContraction X x₀) : Wedge x₀ y₀ ≃ₕ Y :=
  wedgeSwap.toHomotopyEquiv.trans (wedgeHomotopyEquivLeft h)

def pointedContractionHomotopyEquivUnit
    (h : PointedContraction X x₀) : X ≃ₕ Unit where
  toFun := ContinuousMap.const X ()
  invFun := ContinuousMap.const Unit x₀
  left_inv := ⟨h.homotopy.symm⟩
  right_inv := by
    rw [show (ContinuousMap.const X ()).comp (ContinuousMap.const Unit x₀) =
      ContinuousMap.id Unit by
        apply ContinuousMap.ext
        intro u
        exact Subsingleton.elim _ _]

def UHomotopyEquiv : U ≃ₕ Torus :=
  UModel.toHomotopyEquiv.trans (wedgeHomotopyEquivLeft puncturedCirclePointedContraction)

def VHomotopyEquiv : V ≃ₕ Circle :=
  VModel.toHomotopyEquiv.trans
    (wedgeHomotopyEquivRight puncturedTorusPointedContraction)

def UVHomotopyEquiv : {z // z ∈ U ∩ V} ≃ₕ Unit :=
  UVModel.toHomotopyEquiv.trans
    ((wedgeHomotopyEquivLeft puncturedCirclePointedContraction).trans
      (pointedContractionHomotopyEquivUnit puncturedTorusPointedContraction))


#print axioms U_inter_V
#print axioms UModel
#print axioms VModel
#print axioms UVModel
#print axioms wedgeSwap
#print axioms wedgeHomotopyEquivRight
#print axioms pointedContractionHomotopyEquivUnit
#print axioms UHomotopyEquiv
#print axioms VHomotopyEquiv
#print axioms UVHomotopyEquiv

end ConstructionTargets.TorusCircleWedgeOpenCover

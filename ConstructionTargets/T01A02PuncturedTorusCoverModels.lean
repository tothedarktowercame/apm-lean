import ConstructionTargets.PointedPuncturedCircleContraction

open Set
noncomputable section

namespace ConstructionTargets.T01A02PuncturedTorus

abbrev Torus := Circle × Circle
def circleMinusOne : Circle := ⟨-1, by simp [Submonoid.unitSphere]⟩
def missingPoint : Torus := (circleMinusOne, circleMinusOne)
abbrev X := {z : Torus // z ≠ missingPoint}

def U : Set X := {z | (z.1.1 : ℂ) ≠ -1}
def V : Set X := {z | (z.1.2 : ℂ) ≠ -1}

/-- Exact subtype identifications needed before applying the banked
punctured-circle contractions to the MV cover. -/
structure PuncturedTorusCoverModels where
  U_model : U ≃ₜ
    (ConstructionTargets.PointedPuncturedCircleContraction.PuncturedCircle × Circle)
  V_model : V ≃ₜ
    (Circle × ConstructionTargets.PointedPuncturedCircleContraction.PuncturedCircle)
  intersection_model : {z : X // z ∈ U ∩ V} ≃ₜ
    (ConstructionTargets.PointedPuncturedCircleContraction.PuncturedCircle ×
      ConstructionTargets.PointedPuncturedCircleContraction.PuncturedCircle)

def PuncturedTorusCoverModelsContract : Prop :=
  Nonempty PuncturedTorusCoverModels

theorem models_of_contract (h : PuncturedTorusCoverModelsContract) :
    Nonempty PuncturedTorusCoverModels := h

open ConstructionTargets.PointedPuncturedCircleContraction

def UModel : U ≃ₜ (PuncturedCircle × Circle) where
  toFun z := (⟨z.1.1.1, z.2⟩, z.1.1.2)
  invFun z := ⟨⟨(z.1.1, z.2), by
    intro h
    have h1 := congrArg Prod.fst h
    exact z.1.2 (by simpa [missingPoint, circleMinusOne] using congrArg Subtype.val h1)⟩, z.1.2⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def VModel : V ≃ₜ (Circle × PuncturedCircle) where
  toFun z := (z.1.1.1, ⟨z.1.1.2, z.2⟩)
  invFun z := ⟨⟨(z.1, z.2.1), by
    intro h
    have h2 := congrArg Prod.snd h
    exact z.2.2 (by simpa [missingPoint, circleMinusOne] using congrArg Subtype.val h2)⟩, z.2.2⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def intersectionModel : {z : X // z ∈ U ∩ V} ≃ₜ (PuncturedCircle × PuncturedCircle) where
  toFun z := (⟨z.1.1.1, z.2.1⟩, ⟨z.1.1.2, z.2.2⟩)
  invFun z := ⟨⟨(z.1.1, z.2.1), by
    intro h
    have h1 := congrArg Prod.fst h
    exact z.1.2 (by simpa [missingPoint, circleMinusOne] using congrArg Subtype.val h1)⟩, z.1.2, z.2.2⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem puncturedTorusCoverModels : PuncturedTorusCoverModelsContract :=
  ⟨⟨UModel, VModel, intersectionModel⟩⟩

end ConstructionTargets.T01A02PuncturedTorus

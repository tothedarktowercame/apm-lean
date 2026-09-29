import ConstructionTargets.ProductionOpenCoverMayerVietoris
import ConstructionTargets.T01A02PuncturedTorusCoverModels
import ConstructionTargets.TorusCircleWedgeOpenCover
import ConstructionTargets.SolidTorusHomotopyAndHomology
import ConstructionTargets.CoefficientContractiblePair

open CategoryTheory CategoryTheory.Limits Set
open scoped ContinuousMap
noncomputable section

namespace ConstructionTargets.T01A02PuncturedTorus

abbrev H (n : ℕ) (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

/-- Exact geometric and homological input for the degree-two MV argument on
the once-punctured torus. -/
structure PuncturedTorusDegreeTwoMVCover where
  leftPiece : Set X
  rightPiece : Set X
  left_open : IsOpen leftPiece
  right_open : IsOpen rightPiece
  cover : leftPiece ∪ rightPiece = univ
  left_H2_zero : IsZero (H 2 {z : X // z ∈ leftPiece})
  right_H2_zero : IsZero (H 2 {z : X // z ∈ rightPiece})
  intersection_H1_zero : IsZero (H 1 {z : X // z ∈ leftPiece ∩ rightPiece})

def PuncturedTorusDegreeTwoMVCoverContract : Prop :=
  Nonempty PuncturedTorusDegreeTwoMVCover

theorem cover_of_contract (h : PuncturedTorusDegreeTwoMVCoverContract) :
    Nonempty PuncturedTorusDegreeTwoMVCover := h

open ConstructionTargets.PointedPuncturedCircleContraction
open ConstructionTargets.TorusCircleWedgeOpenCover
open ConstructionTargets.CoefficientContractiblePair
open ConstructionTargets.SolidTorusHomotopyAndHomology

def UHomotopyEquivCircle : U ≃ₕ Circle :=
  UModel.toHomotopyEquiv.trans
    (((pointedContractionHomotopyEquivUnit puncturedCirclePointedContraction).prodCongr
      (ContinuousMap.HomotopyEquiv.refl Circle)).trans
        (Homeomorph.uniqueProd Unit Circle).toHomotopyEquiv)

def VHomotopyEquivCircle : V ≃ₕ Circle :=
  VModel.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl Circle).prodCongr
      (pointedContractionHomotopyEquivUnit puncturedCirclePointedContraction)).trans
        (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv)

def intersectionHomotopyEquivUnit : {z : X // z ∈ U ∩ V} ≃ₕ Unit :=
  intersectionModel.toHomotopyEquiv.trans
    (pointedContractionHomotopyEquivUnit puncturedTorusPointedContraction)

theorem U_open : IsOpen U := by
  rw [U]
  exact isOpen_ne.preimage
    (by fun_prop : Continuous fun z : X => (z.1.1 : ℂ))

theorem V_open : IsOpen V := by
  rw [V]
  exact isOpen_ne.preimage
    (by fun_prop : Continuous fun z : X => (z.1.2 : ℂ))

theorem cover : U ∪ V = univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_contra h
  rw [U, V] at h
  push_neg at h
  have h1 : (z.1.1 : ℂ) = -1 := by
    simpa only [Set.mem_setOf_eq, not_ne_iff] using h.1
  have h2 : (z.1.2 : ℂ) = -1 := by
    simpa only [Set.mem_setOf_eq, not_ne_iff] using h.2
  exact z.2 (by
    apply Prod.ext
    · apply Subtype.ext
      simpa [missingPoint, circleMinusOne] using h1
    · apply Subtype.ext
      simpa [missingPoint, circleMinusOne] using h2)

theorem U_H2_zero : IsZero (H 2 U) :=
  (circleModuleHomology_isZero_of_one_lt 2 (by omega)).of_iso
    (singularHomologyIsoOfHomotopyEquiv ℤ UHomotopyEquivCircle 2)

theorem V_H2_zero : IsZero (H 2 V) :=
  (circleModuleHomology_isZero_of_one_lt 2 (by omega)).of_iso
    (singularHomologyIsoOfHomotopyEquiv ℤ VHomotopyEquivCircle 2)

theorem intersection_H1_zero : IsZero (H 1 {z : X // z ∈ U ∩ V}) :=
  (higher_zero ℤ Unit 1 (by omega)).of_iso
    (singularHomologyIsoOfHomotopyEquiv ℤ intersectionHomotopyEquivUnit 1)

theorem puncturedTorusDegreeTwoMVCover : PuncturedTorusDegreeTwoMVCoverContract :=
  ⟨⟨U, V, U_open, V_open, cover, U_H2_zero, V_H2_zero,
    intersection_H1_zero⟩⟩

end ConstructionTargets.T01A02PuncturedTorus

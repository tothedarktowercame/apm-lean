import ConstructionTargets.EuclideanSpherePoleOverlapAdapter
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible

open Set
open scoped ContinuousMap

noncomputable section

namespace ConstructionTargets.SphereProductPoleOpenCover

open ConstructionTargets.EuclideanSpherePoleOverlapAdapter
open ConstructionTargets.PuncturedNormedSpaceRadialEquivalence

abbrev S3 := EuclideanSphere 3
abbrev X := S3 × S3

def p : S3 := canonicalPole 3
def northOpen : Set S3 := {x | x ≠ p}
def southOpen : Set S3 := {x | x ≠ -p}
def U : Set X := {z | z.1 ∈ northOpen}
def V : Set X := {z | z.1 ∈ southOpen}

theorem U_isOpen : IsOpen U := isClosed_singleton.isOpen_compl.preimage continuous_fst
theorem V_isOpen : IsOpen V := isClosed_singleton.isOpen_compl.preimage continuous_fst

theorem p_ne_neg : p ≠ -p := by
  intro h
  have hv : p.1 = -p.1 := congrArg Subtype.val h
  have htwo : (2 : ℝ) • p.1 = 0 := by
    calc
      (2 : ℝ) • p.1 = p.1 + p.1 := two_smul ℝ _
      _ = -p.1 + p.1 := congrArg (fun z => z + p.1) hv
      _ = 0 := neg_add_cancel _
  have hz : p.1 = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hn := norm_canonicalPoleVector 3
  change ‖p.1‖ = 1 at hn
  rw [hz, norm_zero] at hn
  norm_num at hn

theorem U_union_V : U ∪ V = Set.univ := by
  ext z
  simp only [U, V, northOpen, southOpen, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  by_cases h : z.1 = p
  · exact Or.inr (by simpa [h] using p_ne_neg)
  · exact Or.inl h

def firstFactorSubtypeHomeomorph (s : Set S3) :
    {z : X // z.1 ∈ s} ≃ₜ s × S3 where
  toFun z := (⟨z.1.1, z.2⟩, z.1.2)
  invFun z := ⟨(z.1.1, z.2), z.1.2⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def northOpenHomeomorphOrthogonal :
    northOpen ≃ₜ (ℝ ∙ canonicalPoleVector 3)ᗮ :=
  (Homeomorph.setCongr (by
    ext x
    change (x ≠ canonicalPole 3) ↔
      (x ≠ polePoint (canonicalPoleVector 3) (norm_canonicalPoleVector 3))
    rfl)).trans
    ((stereographic (norm_canonicalPoleVector 3)).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (by simp)).trans (Homeomorph.Set.univ _)))

def negSphere : S3 ≃ₜ S3 where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def southOpenHomeomorphNorthOpen : southOpen ≃ₜ northOpen where
  toFun x := ⟨-x.1, by
    intro h
    apply x.2
    simpa using congrArg Neg.neg h⟩
  invFun x := ⟨-x.1, by
    intro h
    apply x.2
    simpa using congrArg Neg.neg h⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact neg_neg x.1.1
  right_inv x := by apply Subtype.ext; apply Subtype.ext; exact neg_neg x.1.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def northOpenHomotopyEquivUnit : northOpen ≃ₕ Unit := by
  letI : ContractibleSpace northOpen :=
    northOpenHomeomorphOrthogonal.contractibleSpace
  exact Classical.choice (ContractibleSpace.hequiv_unit northOpen)

def northOpenProductHomotopyEquivS3 : (northOpen × S3) ≃ₕ S3 :=
  (northOpenHomotopyEquivUnit.prodCongr (ContinuousMap.HomotopyEquiv.refl S3)).trans
    (Homeomorph.uniqueProd Unit S3).toHomotopyEquiv

def U_homotopyEquiv_S3 : U ≃ₕ S3 :=
  (firstFactorSubtypeHomeomorph northOpen).toHomotopyEquiv.trans
    northOpenProductHomotopyEquivS3

def V_homotopyEquiv_S3 : V ≃ₕ S3 :=
  (firstFactorSubtypeHomeomorph southOpen).toHomotopyEquiv.trans
    ((southOpenHomeomorphNorthOpen.prodCongr (Homeomorph.refl S3)).toHomotopyEquiv.trans
      northOpenProductHomotopyEquivS3)

def intersectionProductHomeomorph :
    (U ∩ V : Set X) ≃ₜ EuclideanTwoPoleComplement 3 × S3 where
  toFun z := (⟨z.1.1, z.2.1, z.2.2⟩, z.1.2)
  invFun z := ⟨(z.1.1, z.2), ⟨z.1.2.1, z.1.2.2⟩⟩
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def intersectionHomotopyEquivSphereTwoProdSphereThree :
    (U ∩ V : Set X) ≃ₕ EuclideanSphere 2 × S3 :=
  intersectionProductHomeomorph.toHomotopyEquiv.trans
    (euclideanTwoPoleComplementProductHomotopyEquiv 3 S3)

#print axioms U_union_V
#print axioms U_homotopyEquiv_S3
#print axioms V_homotopyEquiv_S3
#print axioms intersectionProductHomeomorph
#print axioms intersectionHomotopyEquivSphereTwoProdSphereThree

end ConstructionTargets.SphereProductPoleOpenCover

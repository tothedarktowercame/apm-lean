import ConstructionTargets.ComplexProjectiveChartTargets
import Mathlib.Topology.Algebra.ConstMulAction

open Set Topology

noncomputable section

namespace ConstructionTargets.T94A08ProjectiveConic

open ConstructionTargets.ProjectiveSpaceTopology

theorem projectiveQuotientMap_isQuotientMap :
    IsQuotientMap (quotientMap ℂ 2) :=
  ⟨surjective_quotientMap ℂ 2, rfl⟩

def unitSmulHomeomorph (a : ℂˣ) :
    NonzeroVectors ℂ 2 ≃ₜ NonzeroVectors ℂ 2 where
  toFun x := a • x
  invFun x := a⁻¹ • x
  left_inv x := by simp
  right_inv x := by simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val : Continuous
      (fun x : NonzeroVectors ℂ 2 => x.1)).const_smul (a : ℂ)
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous fun x : NonzeroVectors ℂ 2 => ((a⁻¹ : ℂˣ) : ℂ) • x.1
    exact (continuous_subtype_val : Continuous
      (fun x : NonzeroVectors ℂ 2 => x.1)).const_smul ((a⁻¹ : ℂˣ) : ℂ)

/-- Exact missing topological input for constructing the affine partial
homeomorphisms: images of open sets of nonzero vectors are open. -/
def ProjectiveQuotientOpenAuthority : Prop :=
  IsOpenMap (quotientMap ℂ 2)

theorem projectiveQuotientOpenAuthority :
    ProjectiveQuotientOpenAuthority := by
  intro U hU
  apply projectiveQuotientMap_isQuotientMap.isOpen_preimage.mp
  rw [show (quotientMap ℂ 2) ⁻¹' ((quotientMap ℂ 2) '' U) =
      ⋃ a : ℂˣ, (a • ·) '' U by
    ext x
    simp only [mem_preimage, mem_image, mem_iUnion]
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨a, ha⟩ :=
        (Projectivization.mk_eq_mk_iff ℂ x.1 y.1 x.2 y.2).mp hxy.symm
      exact ⟨a, y, hy, Subtype.ext ha⟩
    · rintro ⟨a, y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      apply (Projectivization.mk_eq_mk_iff ℂ y.1 x.1 y.2 x.2).mpr
      exact ⟨a⁻¹, by
        have ha := congrArg Subtype.val hxy
        rw [← ha]
        simp⟩]
  exact isOpen_iUnion fun a => (unitSmulHomeomorph a).isOpenMap U hU

end ConstructionTargets.T94A08ProjectiveConic

import Mathlib.Topology.Homotopy.Lifting
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient

open scoped unitInterval
open Set

noncomputable section

namespace ConstructionTargets

open FundamentalGroup

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace A]
variable {p : E → X} (cov : IsCoveringMap p)

def coveringInducedFundamentalGroupMap (e : E) :
    FundamentalGroup E e →* FundamentalGroup X (p e) :=
  FundamentalGroup.map ⟨p, cov.continuous⟩ e

theorem coveringInducedFundamentalGroupMap_injective (e : E) :
    Function.Injective (coveringInducedFundamentalGroupMap cov e) := by
  exact cov.injective_path_homotopic_map e e

private noncomputable instance monodromyAction (e : E) :
    MulAction (FundamentalGroup X (p e)) (p ⁻¹' {p e}) where
  smul γ e' := cov.monodromy γ e'
  one_smul e' := by simpa using congrFun cov.monodromy_refl e'
  mul_smul γ γ' e' := by
    exact cov.monodromy_trans_apply γ' γ e'

noncomputable def coveringFiberEquivCosets [PathConnectedSpace E] (e : E) :
    (FundamentalGroup X (p e) ⧸ (coveringInducedFundamentalGroupMap cov e).range) ≃
      p ⁻¹' {p e} := by
  letI := monodromyAction cov e
  have hstab :
      MulAction.stabilizer (FundamentalGroup X (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) =
        (coveringInducedFundamentalGroupMap cov e).range := by
    ext γ
    constructor
    · intro hγ
      change cov.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩ at hγ
      obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
      let lift := cov.liftPath γ e (by simp)
      have hend : lift 1 = e := by
        simpa [IsCoveringMap.monodromy, lift] using congrArg Subtype.val hγ
      let δ : Path e e := ⟨lift, cov.liftPath_zero _ _ _, hend⟩
      refine ⟨fromPath (.mk δ), ?_⟩
      change FundamentalGroup.map ⟨p, cov.continuous⟩ e (fromPath (.mk δ)) = _
      rw [map_apply, ← Path.Homotopic.Quotient.mk_map]
      congr 1
      ext t
      exact congrFun (cov.liftPath_lifts γ e (by simp)) t
    · rintro ⟨δ, rfl⟩
      change cov.monodromy (FundamentalGroup.map ⟨p, cov.continuous⟩ e δ) ⟨e, rfl⟩ = ⟨e, rfl⟩
      exact cov.monodromy_map δ
  let orbitEquiv :
      MulAction.orbit (FundamentalGroup X (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) ≃
        FundamentalGroup X (p e) ⧸ (coveringInducedFundamentalGroupMap cov e).range :=
    (MulAction.orbitEquivQuotientStabilizer _ _).trans
      (Subgroup.quotientEquivOfEq hstab)
  have horbit :
      MulAction.orbit (FundamentalGroup X (p e)) (⟨e, rfl⟩ : p ⁻¹' {p e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    rintro ⟨e', he'⟩
    change p e' = p e at he'
    let δ := PathConnectedSpace.somePath e e'
    let δp : Path.Homotopic.Quotient (p e) (p e) :=
      ((Path.Homotopic.Quotient.mk δ).map ⟨p, cov.continuous⟩).cast rfl he'.symm
    exact ⟨fromPath δp, by
      change cov.monodromy δp ⟨e, rfl⟩ = ⟨e', he'⟩
      apply Subtype.ext
      simpa [δp, IsCoveringMap.monodromy, Path.Homotopic.Quotient.cast] using
        congrArg Subtype.val (cov.monodromy_map (.mk δ))⟩
  exact orbitEquiv.symm.trans <| (Equiv.setCongr horbit).trans (Equiv.Set.univ _)

theorem coveringFiberCard_eq_index [PathConnectedSpace E] (e : E) :
    Nat.card (p ⁻¹' {p e}) = (coveringInducedFundamentalGroupMap cov e).range.index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (coveringFiberEquivCosets cov e).symm

theorem coveringFiniteIndex_of_finiteFiber [PathConnectedSpace E] (e : E)
    [Finite (p ⁻¹' {p e})] :
    (coveringInducedFundamentalGroupMap cov e).range.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff_finite_quotient]
  exact Finite.of_equiv _ (coveringFiberEquivCosets cov e).symm

theorem coveringExistsUniqueLift_of_range_le
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (e₀ : E) (he : p e₀ = f a₀)
    (hle : (FundamentalGroup.map f a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  cov.existsUnique_continuousMap_lifts_of_range_le he hle

end ConstructionTargets

import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocPathConnected

open Topology

namespace ConstructionTargets.DeckGroupQuotientFundamentalGroup

/-- The orbit projection of a free properly discontinuous action is a covering
map under the separation and local compactness hypotheses used by Mathlib's
quotient-covering construction. -/
theorem quotientMk_isCoveringMap
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) :
    IsCoveringMap
      (Quotient.mk (MulAction.orbitRel G X) :
        X → MulAction.orbitRel.Quotient G X) := by
  letI : IsCancelSMul G X :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr free
  exact
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := G) (E := X)).isCoveringMap

private abbrev CounterexampleGroup := Multiplicative (ZMod 2)

private instance : TopologicalSpace CounterexampleGroup := ⊤

private instance : ContractibleSpace CounterexampleGroup := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨1, ⟨?_⟩⟩
  exact
    { toFun := fun tx ↦ if tx.1 = 0 then tx.2 else 1
      continuous_toFun := continuous_of_indiscreteTopology
      map_zero_left := fun x ↦ by simp
      map_one_left := fun x ↦ by simp }

private instance : MulAction.IsPretransitive CounterexampleGroup CounterexampleGroup where
  exists_smul_eq x y := ⟨y * x⁻¹, by simp⟩

/-- The regular action of the two-element group on itself with the indiscrete
topology satisfies the fixed theorem's hypotheses, but its orbit quotient is a
singleton and hence has trivial fundamental group. -/
theorem indiscreteRegularAction_no_fundamentalGroupEquiv :
    ¬ Nonempty
      (FundamentalGroup
          (MulAction.orbitRel.Quotient CounterexampleGroup CounterexampleGroup)
          (Quotient.mk _ (1 : CounterexampleGroup)) ≃* CounterexampleGroup) := by
  letI : Subsingleton
      (MulAction.orbitRel.Quotient CounterexampleGroup CounterexampleGroup) :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).mp inferInstance
  intro h
  haveI : Subsingleton
      (FundamentalGroup
        (MulAction.orbitRel.Quotient CounterexampleGroup CounterexampleGroup)
        (Quotient.mk _ (1 : CounterexampleGroup))) := by
    change Subsingleton (Path.Homotopic.Quotient _ _)
    infer_instance
  have heq : h.some.symm (Multiplicative.ofAdd (1 : ZMod 2)) =
      h.some.symm (Multiplicative.ofAdd 0) := Subsingleton.elim _ _
  have hone : (1 : ZMod 2) ≠ 0 := by decide
  exact hone (Multiplicative.ofAdd.injective (h.some.symm.injective heq))

/-- The program's frozen final statement is false without a separation
hypothesis: the indiscrete regular action supplies a concrete counterexample. -/
theorem freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv_refuted :
    ¬ (∀ {G X : Type} [Group G] [TopologicalSpace X] [MulAction G X]
        [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X],
        (∀ g : G, ∀ x : X, g • x = x → g = 1) →
        ∀ [SimplyConnectedSpace X] [LocPathConnectedSpace X] (x : X),
          Nonempty
            (FundamentalGroup (MulAction.orbitRel.Quotient G X)
              (Quotient.mk _ x) ≃* G)) := by
  intro claimed
  apply indiscreteRegularAction_no_fundamentalGroupEquiv
  apply claimed (G := CounterexampleGroup) (X := CounterexampleGroup)
  · intro g x h
    have := congrArg (fun y ↦ y * x⁻¹) h
    simpa [smul_eq_mul] using this

#print axioms quotientMk_isCoveringMap
#print axioms indiscreteRegularAction_no_fundamentalGroupEquiv
#print axioms freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv_refuted

end ConstructionTargets.DeckGroupQuotientFundamentalGroup

import Mathlib
import ConstructionTargets.StatementSurfaceModels

/-! # Generic closing lemmas for t93J03

The Klein-bottle-specific library obligations supply a cover and an exact
subgroup equality.  These lemmas contain the already proved generic lifting
and embedding arguments used after that equality is available.
-/

open ConstructionTargets.StatementSurfaceModels Set
noncomputable section
namespace ConstructionTargets.t93J03Closure

def subspaceInclusion (X : Set KleinBottle) : C(X, KleinBottle) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Rewrite an exact covering subgroup computation and apply the standard
covering-space lifting criterion. -/
theorem coveringLift_of_subgroup_le
    {G C : Type} [Group G] [TopologicalSpace C] {p : C → KleinBottle}
    (hp : IsCoveringMap p) (c : C) {k : KleinBottle} (hpc : p c = k)
    (e : FundamentalGroup KleinBottle k ≃* G) (H : Subgroup G)
    (hcover :
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range =
        Subgroup.comap e.toMonoidHom H)
    (X : Set KleinBottle) [PathConnectedSpace X] [LocPathConnectedSpace X]
    (x : X) (hx : (x : KleinBottle) = k)
    (hX : ∀ g ∈ (FundamentalGroup.mapOfEq (subspaceInclusion X) hx).range,
      e g ∈ H) :
    ∃ l : C(X, C), p ∘ l = subspaceInclusion X := by
  cases hx
  have hle :
      (FundamentalGroup.map (subspaceInclusion X) x).range ≤
        (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ hpc).range := by
    rintro g ⟨y, rfl⟩
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective y
    rw [hcover]
    apply hX
    refine ⟨FundamentalGroup.fromPath (.mk γ), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    congr
  obtain ⟨l, ⟨_, hl⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts_of_range_le hpc hle
  exact ⟨l, hl⟩

/-- A lift of a subtype inclusion is an embedding by cancellation; composing
with an embedding of the covering space preserves embedding. -/
theorem lift_isEmbedding_assembly
    {C : Type} [TopologicalSpace C] {p : C → KleinBottle}
    (hp : Continuous p) (jC : C(C, ℝ × ℝ))
    (hjC : Topology.IsEmbedding jC)
    (X : Set KleinBottle) (l : C(X, C))
    (hl : p ∘ l = subspaceInclusion X) :
    ∃ j : C(X, ℝ × ℝ), Topology.IsEmbedding j := by
  have hl' : Topology.IsEmbedding l := by
    apply Topology.IsEmbedding.of_comp l.continuous hp
    rw [hl]
    exact Topology.IsEmbedding.subtypeVal
  exact ⟨jC.comp l, hjC.comp hl'⟩

#print axioms coveringLift_of_subgroup_le
#print axioms lift_isEmbedding_assembly

end ConstructionTargets.t93J03Closure

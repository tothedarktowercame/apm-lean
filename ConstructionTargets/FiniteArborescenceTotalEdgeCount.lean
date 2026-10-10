import ConstructionTargets.FiniteArborescenceTotalArrowEquivalence
import ConstructionTargets.FiniteSchreierChosenGeneratorEdgeCoordinates

open Quiver CategoryTheory CategoryTheory.ActionCategory

namespace FiniteArborescenceEdgeCount

universe u v

theorem total_card (V : Type u) [Quiver.{v} V] [Arborescence V]
    [Finite V] :
    Nat.card (Quiver.Total V) = Nat.card V - 1 := by
  rw [Nat.card_congr (FiniteArborescenceTotalArrow.totalEquivNonroot V)]
  letI := Fintype.ofFinite V
  letI := Classical.decEq V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

namespace Schreier

open ConstructionTargets.FiniteSchreierChosenGeneratorEdgeCoordinates

def actionEquiv (r : ℕ) (H : Subgroup (G r)) : AG r H ≃ V r H where
  toFun := ActionCategory.back
  invFun := fun x => (x : AG r H)
  left_inv x := by rcases x with ⟨u, x⟩; rcases u with ⟨⟩; rfl
  right_inv _ := rfl

@[reducible] noncomputable def rootedConnected (r : ℕ) (H : Subgroup (G r))
    (base : Gen r H) :
    @RootedConnected (Symmetrify (Gen r H)) _ (show Symmetrify (Gen r H) from base) := by
  refine ⟨fun b => IsFreeGroupoid.path_nonempty_of_hom (G := AG r H) ?_⟩
  rcases MulAction.exists_smul_eq (G r) base.back b.back with ⟨g, hg⟩
  exact ⟨⟨g, hg⟩⟩

noncomputable def tree (r : ℕ) (H : Subgroup (G r))
    (base : Gen r H) : WideSubquiver (Symmetrify (Gen r H)) := by
  letI := rootedConnected r H base
  exact geodesicSubtree (show Symmetrify (Gen r H) from base)

theorem tree_total_card (r n : ℕ) (hn : 0 < n) (H : Subgroup (G r))
    (hindex : H.index = n) (base : Gen r H) :
    Nat.card (Quiver.Total (tree r H base)) = n - 1 := by
  letI := vertexFintype r n hn H hindex
  letI := rootedConnected r H base
  unfold tree
  let T := geodesicSubtree (show Symmetrify (Gen r H) from base)
  let e : T ≃ V r H := actionEquiv r H
  letI : Fintype T := Fintype.ofEquiv (V r H) e.symm
  rw [total_card]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, vertex_card hn H hindex]

end Schreier

#print axioms total_card
#print axioms Schreier.tree_total_card

end FiniteArborescenceEdgeCount

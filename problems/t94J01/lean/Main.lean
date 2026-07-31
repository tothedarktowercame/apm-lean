import Mathlib
import ApmCanaries.Frames.T94J01.Apm_v2_t94J01_1775010781379.Scratch

noncomputable section

open scoped Topology
open Set

namespace ApmCanaries.Frames.T94J01.Apm_v2_t94J01_1775010781379.Main

/-- A finite ladder connecting two points through an open cover. -/
structure LadderChain {X : Type*} (U : Set (Set X)) (p q : X) where
  length : ℕ
  chain : Fin (length + 1) → Set X
  cover_mem : ∀ i, chain i ∈ U
  first_mem : p ∈ chain 0
  last_mem :
    q ∈ chain ⟨length, by exact Nat.lt_succ_self length⟩
  overlap :
    ∀ i : Fin length,
      (chain (Fin.castSucc i) ∩ chain i.succ).Nonempty

/-- The ladder-connectedness predicate. -/
def LadderConnectedSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (U : Set (Set X)),
    (∀ s ∈ U, IsOpen s) →
      ⋃₀ U = (Set.univ : Set X) →
        ∀ p q : X, Nonempty (LadderChain U p q)

/-- Subsingleton spaces are trivially ladder connected. -/
lemma ladderConnected_of_subsingleton
    (X : Type*) [TopologicalSpace X] [Subsingleton X] :
    LadderConnectedSpace X := by
  classical
  intro U hUopen hcover p q
  have hp : p ∈ ⋃₀ U := by simpa [hcover] using (mem_univ p)
  rcases mem_sUnion.1 hp with ⟨V, hVmem, hpV⟩
  refine ⟨⟨0, fun _ => V, ?_, ?_, ?_, ?_⟩⟩
  · intro _; simpa using hVmem
  · simpa using hpV
  · simpa [Subsingleton.elim q p] using hpV
  · intro i; exact Fin.elim0 i

variable {X : Type*} [TopologicalSpace X]

/-- Placeholder: ladder connected ⇒ connected. -/
theorem connected_of_ladderConnected
    (h : LadderConnectedSpace X) :
    IsConnected (Set.univ : Set X) := by
  classical
  -- TODO: formalize the argument that the set of points reachable from a basepoint
  -- via ladders is both open and closed, hence everything.
  sorry

/-- Placeholder: connected ⇒ ladder connected. -/
theorem ladderConnected_of_connected
    (h : IsConnected (Set.univ : Set X)) :
    LadderConnectedSpace X := by
  classical
  -- TODO: construct ladders between any two points by working inside the connected component
  -- cover and extending chains along intersecting open sets.
  sorry

/-- Main equivalence: a space is connected iff it is ladder connected. -/
theorem connected_iff_ladderConnected :
    IsConnected (Set.univ : Set X) ↔ LadderConnectedSpace X := by
  constructor
  · intro hconn
    exact ladderConnected_of_connected (X := X) hconn
  · intro hladder
    exact connected_of_ladderConnected (X := X) hladder

end ApmCanaries.Frames.T94J01.Apm_v2_t94J01_1775010781379.Main

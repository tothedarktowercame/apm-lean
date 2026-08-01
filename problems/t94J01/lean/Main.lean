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

namespace LadderChain

/-- Append one member of the cover to a ladder. -/
def snoc {X : Type*} {U : Set (Set X)} {p q r : X}
    (C : LadderChain U p q) {V : Set X} (hVU : V ∈ U)
    (hqV : q ∈ V) (hrV : r ∈ V) : LadderChain U p r where
  length := C.length + 1
  chain := Fin.snoc C.chain V
  cover_mem i := by
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hVU
    | cast j => simpa only [Fin.snoc_castSucc] using C.cover_mem j
  first_mem := by simpa only [Fin.snoc_castSucc] using C.first_mem
  last_mem := by
    change r ∈ @Fin.snoc (C.length + 1) (fun _ ↦ Set X) C.chain V
      (Fin.last (C.length + 1))
    simpa only [Fin.snoc_last] using hrV
  overlap i := by
    induction i using Fin.lastCases with
    | last =>
        rw [show (Fin.last C.length).succ = Fin.last (C.length + 1) by rfl,
          Fin.snoc_last, Fin.snoc_castSucc]
        exact ⟨q, C.last_mem, hqV⟩
    | cast j =>
        simpa only [Fin.snoc_castSucc, Fin.succ_castSucc] using C.overlap j

end LadderChain

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

/-- Ladder connectedness rules out a separation, including for the empty
space. -/
-- STATEMENT REPAIR 2026-08-01 (Joe-authorised): use `IsPreconnected`, which
-- matches the source's separation-based convention without adding a
-- nonemptiness assumption absent from the printed problem.
theorem connected_of_ladderConnected
    (h : LadderConnectedSpace X) :
    IsPreconnected (Set.univ : Set X) := by
  classical
  intro u v hu hv huv ⟨p, _, hp⟩ ⟨q, _, hq⟩
  have hcover : ⋃₀ ({u, v} : Set (Set X)) = (Set.univ : Set X) := by
    rw [sUnion_pair, eq_univ_iff_forall]
    exact fun x ↦ huv (mem_univ x)
  obtain ⟨C⟩ := h ({u, v} : Set (Set X)) (by
    intro s hs
    simp only [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hu
    · exact hv) hcover p q
  have hinv : ∀ i : Fin (C.length + 1),
      (u ∩ v).Nonempty ∨ C.chain i = u := by
    intro i
    induction i using Fin.induction with
    | zero =>
        have hmem := C.cover_mem 0
        simp only [mem_insert_iff, mem_singleton_iff] at hmem
        rcases hmem with hcu | hcv
        · exact Or.inr hcu
        · exact Or.inl ⟨p, hp, hcv ▸ C.first_mem⟩
    | succ i ih =>
        rcases ih with huv' | hprev
        · exact Or.inl huv'
        have hmem := C.cover_mem i.succ
        simp only [mem_insert_iff, mem_singleton_iff] at hmem
        rcases hmem with hnext | hnext
        · exact Or.inr hnext
        · rcases C.overlap i with ⟨z, hzprev, hznext⟩
          exact Or.inl ⟨z, hprev ▸ hzprev, hnext ▸ hznext⟩
  rcases hinv (Fin.last C.length) with huv' | hlast
  · simpa using huv'
  · exact ⟨q, mem_univ q, hlast ▸ C.last_mem, hq⟩

/-- A space with no separation is ladder connected. -/
theorem ladderConnected_of_connected
    (h : IsPreconnected (Set.univ : Set X)) :
    LadderConnectedSpace X := by
  classical
  intro U hUopen hcover p q
  let Adj : X → X → Prop := fun x y ↦
    ∃ V ∈ U, x ∈ V ∧ y ∈ V
  have hAdj_symm : Symmetric Adj := by
    rintro x y ⟨V, hVU, hxV, hyV⟩
    exact ⟨V, hVU, hyV, hxV⟩
  have hreach : Relation.ReflTransGen Adj p q := by
    apply h.induction₂ (Relation.ReflTransGen Adj)
    · intro x _
      have hx : x ∈ ⋃₀ U := by simpa [hcover]
      rcases mem_sUnion.1 hx with ⟨V, hVU, hxV⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds ((hUopen V hVU).mem_nhds hxV)] with y hy
      exact Relation.ReflTransGen.single ⟨V, hVU, hxV, hy⟩
    · intro x y z _ _ _ hxy hyz
      exact hxy.trans hyz
    · intro x y _ _ hxy
      exact (Relation.ReflTransGen.symmetric hAdj_symm) hxy
    · simp
    · simp
  have toChain {x y : X} (hr : Relation.ReflTransGen Adj x y) :
      Nonempty (LadderChain U x y) := by
    induction hr with
    | refl =>
        have hx : x ∈ ⋃₀ U := by simpa [hcover]
        rcases mem_sUnion.1 hx with ⟨V, hVU, hxV⟩
        exact ⟨⟨0, fun _ ↦ V, fun _ ↦ hVU, hxV, hxV, fun i ↦ Fin.elim0 i⟩⟩
    | tail hxy hyz ih =>
        rcases ih with ⟨C⟩
        rcases hyz with ⟨V, hVU, hyV, hzV⟩
        exact ⟨C.snoc hVU hyV hzV⟩
  exact toChain hreach

/-- Main equivalence: a space is connected iff it is ladder connected. -/
-- STATEMENT REPAIR 2026-08-01 (Joe-authorised): use the empty-space-compatible
-- Mathlib notion corresponding to the printed problem's separation definition.
theorem connected_iff_ladderConnected :
    IsPreconnected (Set.univ : Set X) ↔ LadderConnectedSpace X := by
  constructor
  · intro hconn
    exact ladderConnected_of_connected (X := X) hconn
  · intro hladder
    exact connected_of_ladderConnected (X := X) hladder

end ApmCanaries.Frames.T94J01.Apm_v2_t94J01_1775010781379.Main

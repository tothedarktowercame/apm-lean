import Mathlib
import ApmCanaries.Frames.B96J01.Apm_v2_b96J01_1775006550462.Scratch

noncomputable section

open scoped BigOperators

open Equiv Equiv.Perm

namespace ApmCanaries.Frames.B96J01.Apm_v2_b96J01_1775006550462.Main

/-!
We show that a subgroup of `S₅` containing a 5-cycle and a transposition must
equal the whole symmetric group.  The heavy lifting is delegated to Mathlib's
`closure_prime_cycle_swap`, which states that any prime cycle together with any
transposition generates the full symmetric group on a prime number of points.
-/

lemma five_cycle_transposition_generate
    (G : Subgroup (Equiv.Perm (Fin 5)))
    {σ τ : Equiv.Perm (Fin 5)}
    (hσ_cycle : IsCycle σ) (hσ_ord : orderOf σ = 5) (hσ_mem : σ ∈ G)
    (hτ_swap : IsSwap τ) (hτ_mem : τ ∈ G) :
    G = ⊤ := by
  classical
  -- the 5-cycle moves every point, so its support is the whole universe
  have hσ_support : σ.support = (Finset.univ : Finset (Fin 5)) := by
    apply Finset.eq_univ_of_card
    simp [hσ_cycle.orderOf, hσ_ord, Finset.card_univ]
  -- the closure of σ and τ is the whole symmetric group on five points
  have hclosure :
      closure ({σ, τ} : Set (Equiv.Perm (Fin 5))) = (⊤ : Subgroup _) := by
    have hprime : (Fintype.card (Fin 5)).Prime := by decide
    simpa using
      closure_prime_cycle_swap (σ := σ) (τ := τ) hprime hσ_cycle hσ_support hτ_swap
  -- since σ and τ lie in G, their closure is contained in G
  have hclosure_le : closure ({σ, τ} : Set (Equiv.Perm (Fin 5))) ≤ G := by
    refine closure_le ?_
    intro g hg
    simp [Set.mem_insert_iff, Set.mem_singleton_iff, hσ_mem, hτ_mem] at hg
    exact hg
  -- therefore top ≤ G, forcing equality
  have : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≤ G := by
    simpa [hclosure] using hclosure_le
  exact le_antisymm (by simpa using this) le_top

/-- A subgroup of `S₅` containing a 5-cycle and a transposition is all of `S₅`. -/
theorem subgroup_eq_top_of_fiveCycle_and_swap
    {G : Subgroup (Equiv.Perm (Fin 5))}
    (hσ : ∃ σ ∈ G, IsCycle σ ∧ orderOf σ = 5)
    (hτ : ∃ τ ∈ G, IsSwap τ) :
    G = ⊤ := by
  obtain ⟨σ, hσ_mem, hσ_cycle, hσ_ord⟩ := hσ
  obtain ⟨τ, hτ_mem, hτ_swap⟩ := hτ
  exact five_cycle_transposition_generate G hσ_cycle hσ_ord hσ_mem hτ_swap hτ_mem

end ApmCanaries.Frames.B96J01.Apm_v2_b96J01_1775006550462.Main

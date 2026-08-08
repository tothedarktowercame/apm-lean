import Mathlib

/-!
# APM b96J01 — a five-cycle and a transposition generate `S₅`

The hypotheses use Mathlib's genuine cycle and swap predicates together with
membership in an actual subgroup of `Equiv.Perm (Fin 5)`.  The conclusion says
that subgroup is the full symmetric group.

## Statement repairs

None.

## Encoding questions

None.
-/

theorem apm_b96j01
    {G : Subgroup (Equiv.Perm (Fin 5))}
    (hσ : ∃ σ ∈ G, Equiv.Perm.IsCycle σ ∧ orderOf σ = 5)
    (hτ : ∃ τ ∈ G, Equiv.Perm.IsSwap τ) :
    G = ⊤ := by
  obtain ⟨σ, hσG, hσcycle, hσorder⟩ := hσ
  obtain ⟨τ, hτG, hτswap⟩ := hτ
  have hprime : Nat.Prime (Fintype.card (Fin 5)) := by norm_num
  have hsupport : σ.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    calc
      σ.support.card = orderOf σ := hσcycle.orderOf.symm
      _ = 5 := hσorder
      _ = Fintype.card (Fin 5) := by simp
  have hclosure : Subgroup.closure ({σ, τ} : Set (Equiv.Perm (Fin 5))) = ⊤ :=
    Equiv.Perm.closure_prime_cycle_swap hprime hσcycle hsupport hτswap
  rw [eq_top_iff, ← hclosure, Subgroup.closure_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  exact ⟨hσG, hτG⟩

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
  sorry

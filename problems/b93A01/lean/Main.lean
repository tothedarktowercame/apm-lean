import Mathlib

/-!
# APM b93A01 — groups of order `pq` and faithful permutation degree

## Statement repairs

None.

## Encoding notes

“Isomorphic to a subgroup of `Sₙ`” is represented by a multiplicative
homomorphism with an injective underlying function into `Equiv.Perm (Fin n)`.
Thus the non-embedding conclusions retain
faithfulness, rather than merely asserting that no particular action works.
-/

def apm_b93a01_embeds (G H : Type) [Group G] [Group H] : Prop :=
  ∃ f : G →* H, Function.Injective f

theorem apm_b93a01
    (G : Type) [Group G] [Fintype G] (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Fintype.card G = p * q) :
    (∃ Q : Subgroup G, Q.Normal ∧ Nat.card Q = q) ∧
    ((∃ P : Subgroup G, P.Normal ∧ Nat.card P = p) →
      ∀ a b : G, a * b = b * a) ∧
    ((¬∀ a b : G, a * b = b * a) →
      apm_b93a01_embeds G (Equiv.Perm (Fin q)) ∧
      ¬apm_b93a01_embeds G (Equiv.Perm (Fin (q - 1)))) ∧
    ((∀ a b : G, a * b = b * a) →
      apm_b93a01_embeds G (Equiv.Perm (Fin (p + q))) ∧
      ¬apm_b93a01_embeds G (Equiv.Perm (Fin (p + q - 1)))) := by
  have hnoSmallNonabelian :
      ¬apm_b93a01_embeds G (Equiv.Perm (Fin (q - 1))) := by
    rintro ⟨f, hf⟩
    have hdvd : Nat.card G ∣ Nat.card (Equiv.Perm (Fin (q - 1))) :=
      Subgroup.card_dvd_of_injective f hf
    rw [Nat.card_eq_fintype_card, hcard, Nat.card_perm, Nat.card_fin] at hdvd
    have hqmul : q ∣ p * q := by
      exact ⟨p, by simp [mul_comm]⟩
    have hqfac : q ∣ (q - 1).factorial := hqmul.trans hdvd
    have hle : q ≤ q - 1 := (hq.dvd_factorial).mp hqfac
    omega
  /- PASS-1 boundary: `hnoSmallNonabelian` proves the sharp obstruction
     `G ↪ Equiv.Perm (Fin (q - 1))` is impossible, using
     `card_dvd_of_injective`, `Nat.card_perm`, and
     `Nat.Prime.dvd_factorial`.  I also searched the `Sylow` API, including
     `Sylow.card_eq_multiplicity`, `card_sylow_modEq_one`, and
     `Sylow.normal_of_subsingleton`.  The remaining formalization needs the
     order-`p*q` Sylow count, faithfulness of the coset action in the
     nonabelian case, and the exact minimal-degree cycle argument for the
     abelian case; I could not complete those bridges in pass 1. -/
  sorry

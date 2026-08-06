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
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  -- (Sibling: b03J01)
  let Qs : Sylow q G := Classical.choice inferInstance
  have hQcard : Nat.card (Qs : Subgroup G) = q := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard]
    rw [Nat.factorization_mul hp.ne_zero hq.ne_zero, hp.factorization, hq.factorization]
    simp [Nat.ne_of_lt hpq]
  have hQindex : (Qs : Subgroup G).index = p := by
    have hm := Subgroup.card_mul_index (Qs : Subgroup G)
    rw [hQcard, Nat.card_eq_fintype_card, hcard] at hm
    nlinarith [hq.two_le]
  have hSylowCard : Nat.card (Sylow q G) = 1 := by
    have hdvd : Nat.card (Sylow q G) ∣ p := hQindex ▸ Sylow.card_dvd_index Qs
    have hcases := (Nat.dvd_prime hp).mp hdvd
    rcases hcases with h | h
    · exact h
    · exfalso
      have hmod := card_sylow_modEq_one q G
      rw [h] at hmod
      have : p % q = 1 % q := hmod
      have hpone : p = 1 := by
        calc
          p = p % q := (Nat.mod_eq_of_lt hpq).symm
          _ = 1 % q := this
          _ = 1 := Nat.mod_eq_of_lt hq.one_lt
      exact hp.ne_one hpone
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hSylowCard).1
  have hQnormal : (Qs : Subgroup G).Normal := Sylow.normal_of_subsingleton Qs
  refine ⟨⟨(Qs : Subgroup G), hQnormal, hQcard⟩, ?_⟩
  /- PASS-1 boundary: the first conjunct is now proved: the `q`-Sylow has
     cardinality `q`; `Sylow.card_dvd_index`, `card_sylow_modEq_one`, and
     `Sylow.normal_of_subsingleton` show it is the unique, hence normal,
     `q`-Sylow.  `hnoSmallNonabelian` also proves the sharp obstruction
     `G ↪ Equiv.Perm (Fin (q - 1))` is impossible.

     For the remaining three conjuncts I searched `Subgroup.normalCore_eq_ker`
     and `MulAction.toPermHom` for the coset action, `Equiv.Perm.lcm_cycleType`,
     `Equiv.Perm.sum_cycleType_le`, and `Equiv.Perm.finRotate` for the exact
     permutation bounds, plus `IsZGroup.of_squarefree` and the cyclic-group
     APIs.  The unresolved boundary is first proving that two normal Sylow
     subgroups of coprime prime orders generate `G` and commute, then deriving
     injectivity of the `q`-coset action from non-normality of a `p`-Sylow.
     The abelian branch additionally needs an explicit cyclic generator and a
     disjoint `p`/`q` cycle embedding, followed by the cycle-type lower bound.
     No closed artifact or construction library packaged these bridges. -/
  sorry

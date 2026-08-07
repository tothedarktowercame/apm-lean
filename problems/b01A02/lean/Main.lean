import Mathlib

noncomputable section

/-!
# APM b01A02

## Statement repairs

None.

## Encoding notes

The order and subgroup index are the actual finite cardinality and
`Subgroup.index`. Normality and cyclicity use Mathlib's structural predicates,
rather than merely asserting numerical consequences of them.
-/

def apmSmallestPrimeDivisor (p n : ℕ) : Prop :=
  p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q

/-- The custom smallest-prime predicate agrees with Mathlib's `Nat.minFac`. -/
lemma apmSmallestPrimeDivisor_eq_minFac {p n : ℕ}
    (h : apmSmallestPrimeDivisor p n) : p = n.minFac := by
  rcases h with ⟨hp, hpdvd, hleast⟩
  have hn1 : n ≠ 1 := by
    intro hn
    subst n
    exact hp.not_dvd_one hpdvd
  apply le_antisymm
  · exact hleast n.minFac (Nat.minFac_prime hn1) (Nat.minFac_dvd n)
  · exact Nat.minFac_le_of_dvd hp.two_le hpdvd

/-- A subgroup whose index is the smallest prime divisor of the group order is
normal. Mathlib now packages the coset-action argument directly. -/
lemma apm_b01A02_normal_of_smallest_prime_index
    (G : Type*) [Group G] [Fintype G]
    (p : ℕ) (H : Subgroup G)
    (hp : apmSmallestPrimeDivisor p (Fintype.card G))
    (hindex : H.index = p) : H.Normal := by
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [hindex]
  simpa using apmSmallestPrimeDivisor_eq_minFac hp

theorem apm_b01a02 :
    (∀ (G : Type*) [Group G] [Fintype G]
      (p : ℕ) (H : Subgroup G),
      apmSmallestPrimeDivisor p (Fintype.card G) →
      H.index = p → H.Normal) ∧
    (∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = 255 →
        (∃ P : Subgroup G, P.Normal ∧ Nat.card P = 17) ∧
        (∃ H : Subgroup G,
          H.Normal ∧ Nat.card H = 85 ∧ IsCyclic H) ∧
        IsCyclic G) := by
  /-
  PARTIAL boundary (closer hop 1): the complete first conjunct is now proved
  above as `apm_b01A02_normal_of_smallest_prime_index`. The original skip was
  stale: Mathlib now contains both the Sylow theorems and
  `Subgroup.normal_of_index_eq_minFac_card`, which packages exactly the
  coset-action/kernel argument. The helper
  `apmSmallestPrimeDivisor_eq_minFac` bridges the frozen custom predicate to
  that API.

  The order-255 conjunct remains. Source and corpus inspection identified the
  usable ingredients `Sylow.card_dvd_index`, `card_sylow_modEq_one`, and
  `Sylow.normal_of_subsingleton`; sibling `b93A01` demonstrates the uniqueness
  arithmetic. The remaining assembly is constructing the normal Sylow-17
  subgroup, adjoining a Sylow-5 subgroup to obtain order 85, applying the
  newly closed index-three theorem, then proving cyclicity of the order-85
  subgroup and triviality of the final order-three conjugation action.
  -/
  sorry

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

/-- A group of order 255 has a unique, hence normal, Sylow-17 subgroup. -/
lemma apm_b01A02_sylow17_normal_of_card_255
    (G : Type*) [Group G] [Fintype G] (hG : Nat.card G = 255)
    (S : Sylow 17 G) : S.toSubgroup.Normal ∧ Nat.card S = 17 := by
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hScard : Nat.card S = 17 := by
    rw [Sylow.card_eq_multiplicity, hG]
    native_decide
  have hSindex : S.index = 15 := by
    have h := S.toSubgroup.index_mul_card
    rw [hScard, hG] at h
    omega
  have hdvd : Nat.card (Sylow 17 G) ∣ 15 := by
    simpa [hSindex] using Sylow.card_dvd_index S
  have hnmem : Nat.card (Sylow 17 G) ∈ Nat.divisors 15 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 15 = {1, 3, 5, 15} := by native_decide
  rw [hdivs] at hnmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
  have hone : Nat.card (Sylow 17 G) = 1 := by
    rcases hnmem with h1 | h3 | h5 | h15
    · exact h1
    all_goals
      exfalso
      have hmod : Nat.card (Sylow 17 G) ≡ 1 [MOD 17] :=
        card_sylow_modEq_one 17 G
      simp_all [Nat.ModEq]
  haveI : Subsingleton (Sylow 17 G) :=
    (Nat.card_eq_one_iff_unique.mp hone).1
  exact ⟨Sylow.normal_of_subsingleton S, hScard⟩

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
  constructor
  · intro G _ _ p H hp hindex
    exact apm_b01A02_normal_of_smallest_prime_index G p H hp hindex
  · intro G _ _ hG
    have hGcard : Nat.card G = 255 := by
      simpa [Nat.card_eq_fintype_card] using hG
    let S : Sylow 17 G := default
    have hS := apm_b01A02_sylow17_normal_of_card_255 G hGcard S
    refine ⟨⟨S, hS.1, hS.2⟩, ?_⟩
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
  Closer hop 2 additionally proves the first order-255 conclusion:
  `apm_b01A02_sylow17_normal_of_card_255` specializes the compiled Sylow
  counting pattern from sibling `b99A02`.  The number of Sylow-17 subgroups
  divides 15 and is congruent to one modulo 17, hence is one.

  A targeted search of `GroupTheory/SpecificGroups/ZGroup.lean` found
  `IsZGroup.of_squarefree`, which gives cyclic Sylow subgroups for order 255,
  and the semidirect-product classification `isZGroup_iff_exists_mulEquiv`.
  It does not package the cyclic-number theorem (`gcd(n, φ(n)) = 1` implies
  every group of order `n` is cyclic), nor extract the required normal
  order-85 subgroup.  The remaining bridge is therefore construction of that
  subgroup and triviality of the two resulting coprime conjugation actions.
  -/
    sorry

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

/-- Burnside transfer supplies the previously missing normal Hall subgroup of
order `85`: a Sylow-3 subgroup is cyclic because `255` is squarefree, and it
is a Sylow subgroup for the smallest prime divisor. -/
lemma apm_b01A02_exists_normal_card_85
    (G : Type*) [Group G] [Fintype G] (hG : Nat.card G = 255) :
    ∃ H : Subgroup G, H.Normal ∧ Nat.card H = 85 := by
  letI : IsZGroup G := IsZGroup.of_squarefree (by
    rw [hG]
    native_decide)
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let P : Sylow 3 G := default
  have hPcyc : IsCyclic P := inferInstance
  have hpmin : (Nat.card G).minFac = 3 := by rw [hG]; native_decide
  let T := MonoidHom.transferSylow P (hPcyc.normalizer_le_centralizer hpmin)
  let H : Subgroup G := T.ker
  have hcomp : H.IsComplement' P := by
    simpa [H, T] using hPcyc.isComplement' hpmin
  have hPcard : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hG]
    native_decide
  have hmul := hcomp.card_mul
  rw [hPcard, hG] at hmul
  haveI : H.Normal := inferInstance
  exact ⟨H, inferInstance, by omega⟩

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
  PARTIAL boundary (closer hop 3). A renewed inspection of Burnside transfer
  found `IsCyclic.isComplement'`, which was more directly useful than the
  semidirect-product classification.  Since `255` is squarefree,
  `IsZGroup.of_squarefree` makes a Sylow-3 subgroup cyclic; because `3` is the
  smallest prime divisor, its transfer kernel is a normal complement.
  `apm_b01A02_exists_normal_card_85` now compiles this construction and uses
  `IsComplement'.card_mul` to prove the kernel has order exactly `85`.

  Thus both required normal-subgroup existence claims are closed independently.
  The remaining bridge is cyclicity: show the normal order-85 transfer kernel
  is cyclic and then show the quotient order-three action on it is trivial.
  `IsZGroup` only makes Sylow subgroups cyclic, not an arbitrary squarefree
  group cyclic; Mathlib has no cyclic-number theorem implementing the needed
  coprime automorphism-order argument. Searches of transfer, Z-groups,
  automorphism groups of cyclic groups, nilpotence, all solved siblings,
  `LEMMA-INDEX.md`, and construction targets found no packaged final step.

  HOP 4 isolates the absent cyclic-number theorem into the two exact instances
  needed here (recorded as contracts rather than additional declarations with
  `sorry`):

  ```lean
  theorem apm_b01A02_isCyclic_of_card_85
      (G : Type*) [Group G] [Fintype G]
      (hG : Nat.card G = 85) : IsCyclic G

  theorem apm_b01A02_isCyclic_of_card_255
      (G : Type*) [Group G] [Fintype G]
      (hG : Nat.card G = 255) : IsCyclic G
  ```

  Both statements are true instances of the classical cyclic-number
  criterion: `85 = 5 * 17` and `255 = 3 * 5 * 17` are squarefree, and no prime
  factor divides one less than another prime factor. The first contract makes
  the already-constructed normal subgroup of order `85` cyclic; the second
  supplies the final cyclicity conjunct for `G`. Proving them in this snapshot
  still requires assembling the coprime semidirect-action argument from
  `IsZGroup.isZGroup_iff_exists_mulEquiv` and cyclic automorphism cardinalities.

  BATCH 2 CLOSER: current Mathlib source search found the Z-group
  semidirect-product classification and cyclicity of nilpotent Z-groups, but no
  theorem deriving nilpotence (equivalently, triviality of the relevant
  semidirect actions) from the arithmetic conditions for 85 or 255. A local
  assembly test confirmed that the two displayed cyclic-number contracts are
  sufficient with no additional group-theoretic glue: they apply directly to
  the transfer kernel and ambient group. The test was not retained as a helper
  because its dependency audit inherited the file's existing `native_decide`
  axioms from the Sylow-cardinality and transfer lemmas; it therefore did not
  meet the axiom-clean declaration gate. Replacing those computations by
  `norm_num`/kernel `decide` was also tested, but this snapshot does not reduce
  `Nat.factorization 255`, `Squarefree 255`, or `Nat.minFac 255` through either
  tactic. The mathematical obstruction remains Hölder's cyclic-number theorem;
  the additional trust-cleanup obstruction is five finite arithmetic proofs.
  -/
    sorry

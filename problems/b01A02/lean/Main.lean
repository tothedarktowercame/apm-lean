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

## Proof constraints

The proof must be kernel-checked. `#print axioms` on the target declaration
must report exactly `[propext, Classical.choice, Quot.sound]`. `native_decide`
is not acceptable: it discharges the goal through the compiler rather than the
kernel and introduces a `._native.native_decide.` axiom.

A previous attempt (jit-all-open-v2 frame f61) discharged divisor and Sylow
counting steps with `native_decide`, producing five
`._native.native_decide.` axioms in `#print axioms`. That attempt was
rejected and is not recorded as a proof.
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
    rw [show 255 = 3 * (5 * 17) by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      (show Nat.Prime 3 by norm_num).factorization,
      (show Nat.Prime 5 by norm_num).factorization,
      (show Nat.Prime 17 by norm_num).factorization]
    simp
  have hSindex : S.index = 15 := by
    have h := S.toSubgroup.index_mul_card
    rw [hScard, hG] at h
    omega
  have hdvd : Nat.card (Sylow 17 G) ∣ 15 := by
    simpa [hSindex] using Sylow.card_dvd_index S
  have hnmem : Nat.card (Sylow 17 G) ∈ Nat.divisors 15 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 15 = {1, 3, 5, 15} := by decide
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
    ∃ (H : Subgroup G) (P : Sylow 3 G),
      H.Normal ∧ Nat.card H = 85 ∧ Nat.card P = 3 ∧ H.IsComplement' P := by
  letI : IsZGroup G := IsZGroup.of_squarefree (by
    rw [hG, show 255 = 3 * (5 * 17) by norm_num]
    exact (Nat.squarefree_mul (by norm_num)).mpr
      ⟨(show Nat.Prime 3 by norm_num).squarefree,
        (Nat.squarefree_mul (by norm_num)).mpr
          ⟨(show Nat.Prime 5 by norm_num).squarefree,
            (show Nat.Prime 17 by norm_num).squarefree⟩⟩)
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let P : Sylow 3 G := default
  have hPcyc : IsCyclic P := inferInstance
  have hpmin : (Nat.card G).minFac = 3 := by rw [hG]; norm_num
  let T := MonoidHom.transferSylow P (hPcyc.normalizer_le_centralizer hpmin)
  let H : Subgroup G := T.ker
  have hcomp : H.IsComplement' P := by
    simpa [H, T] using hPcyc.isComplement' hpmin
  have hPcard : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hG]
    rw [show 255 = 3 * (5 * 17) by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      (show Nat.Prime 3 by norm_num).factorization,
      (show Nat.Prime 5 by norm_num).factorization,
      (show Nat.Prime 17 by norm_num).factorization]
    simp
  have hmul := hcomp.card_mul
  rw [hPcard, hG] at hmul
  haveI : H.Normal := inferInstance
  exact ⟨H, P, inferInstance, by omega, hPcard, hcomp⟩

/-- Every group of order `85 = 5 * 17` is cyclic.  Sylow arithmetic makes
both Sylow subgroups unique; squarefreeness then upgrades nilpotence to
cyclicity through Mathlib's `IsZGroup` instance. -/
lemma apm_b01A02_isCyclic_of_card_85
    (G : Type*) [Group G] [Fintype G] (hG : Nat.card G = 85) : IsCyclic G := by
  have hsylow5 : Nat.card (Sylow 5 G) = 1 := by
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    let P : Sylow 5 G := default
    have hPcard : Nat.card P = 5 := by
      rw [Sylow.card_eq_multiplicity, hG]
      rw [show 85 = 5 * 17 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        (show Nat.Prime 5 by norm_num).factorization,
        (show Nat.Prime 17 by norm_num).factorization]
      simp
    have hPindex : P.index = 17 := by
      have h := P.toSubgroup.index_mul_card
      rw [hPcard, hG] at h
      omega
    have hdvd : Nat.card (Sylow 5 G) ∣ 17 := by
      simpa [hPindex] using Sylow.card_dvd_index P
    have hnmem : Nat.card (Sylow 5 G) ∈ Nat.divisors 17 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdivs : Nat.divisors 17 = {1, 17} := by decide
    rw [hdivs] at hnmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
    rcases hnmem with h1 | h17
    · exact h1
    · exfalso
      have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] :=
        card_sylow_modEq_one 5 G
      simp_all [Nat.ModEq]
  have hsylow17 : Nat.card (Sylow 17 G) = 1 := by
    letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    let P : Sylow 17 G := default
    have hPcard : Nat.card P = 17 := by
      rw [Sylow.card_eq_multiplicity, hG]
      rw [show 85 = 5 * 17 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
        (show Nat.Prime 5 by norm_num).factorization,
        (show Nat.Prime 17 by norm_num).factorization]
      simp
    have hPindex : P.index = 5 := by
      have h := P.toSubgroup.index_mul_card
      rw [hPcard, hG] at h
      omega
    have hdvd : Nat.card (Sylow 17 G) ∣ 5 := by
      simpa [hPindex] using Sylow.card_dvd_index P
    have hnmem : Nat.card (Sylow 17 G) ∈ Nat.divisors 5 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdivs : Nat.divisors 5 = {1, 5} := by decide
    rw [hdivs] at hnmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
    rcases hnmem with h1 | h5
    · exact h1
    · exfalso
      have hmod : Nat.card (Sylow 17 G) ≡ 1 [MOD 17] :=
        card_sylow_modEq_one 17 G
      simp_all [Nat.ModEq]
  letI : IsZGroup G := IsZGroup.of_squarefree (by
    rw [hG, show 85 = 5 * 17 by norm_num]
    exact (Nat.squarefree_mul (by norm_num)).mpr
      ⟨(show Nat.Prime 5 by norm_num).squarefree,
        (show Nat.Prime 17 by norm_num).squarefree⟩)
  letI : Group.IsNilpotent G :=
    ((isNilpotent_of_finite_tfae (G := G)).out 3 0).mp (by
      intro p hp P
      by_cases hpdvd : p ∣ Nat.card G
      · have hp' : p.Prime := hp.out
        rw [hG] at hpdvd
        have hp85 : p ∣ 5 * 17 := by norm_num; exact hpdvd
        rcases hp'.dvd_mul.mp hp85 with hp5 | hp17
        · have hpEq : p = 5 := (Nat.dvd_prime (by norm_num)).mp hp5 |>.resolve_left hp'.ne_one
          subst p
          letI : Subsingleton (Sylow 5 G) :=
            (Nat.card_eq_one_iff_unique.mp hsylow5).1
          exact Sylow.normal_of_subsingleton P
        · have hpEq : p = 17 := (Nat.dvd_prime (by norm_num)).mp hp17 |>.resolve_left hp'.ne_one
          subst p
          letI : Subsingleton (Sylow 17 G) :=
            (Nat.card_eq_one_iff_unique.mp hsylow17).1
          exact Sylow.normal_of_subsingleton P
      · have hPcard : Nat.card P = 1 := by
          rw [Sylow.card_eq_multiplicity,
            Nat.factorization_eq_zero_of_not_dvd hpdvd, pow_zero]
        haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hPcard).1
        have hPbot : (P : Subgroup G) = ⊥ :=
          (Subgroup.eq_bot_iff_forall _).mpr fun x hx =>
            Subtype.ext_iff.mp (Subsingleton.elim ⟨x, hx⟩ 1)
        rw [hPbot]
        infer_instance)
  infer_instance

/-- A group of order 255 is cyclic.  Transfer splits it as a cyclic group of
order 85 by a cyclic group of order 3, and cardinality forces the conjugation
action to be trivial. -/
lemma apm_b01A02_isCyclic_of_card_255
    (G : Type*) [Group G] [Fintype G] (hG : Nat.card G = 255) : IsCyclic G := by
  rcases apm_b01A02_exists_normal_card_85 G hG with
    ⟨H, P, hHnormal, hHcard, hPcard, hcomp⟩
  letI : Fintype H := Fintype.ofFinite H
  letI : H.Normal := hHnormal
  letI : IsCyclic H := apm_b01A02_isCyclic_of_card_85 H hHcard
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : IsCyclic P := isCyclic_of_card_dvd_prime (by rw [hPcard])
  let φ : P →* MulAut H :=
    H.normalizerMonoidHom.comp
      (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top))
  have hφrange_dvd3 : Nat.card φ.range ∣ 3 := by
    simpa [hPcard] using Subgroup.card_range_dvd φ
  have hφrange_dvd64 : Nat.card φ.range ∣ 64 := by
    have hdvd := φ.range.card_subgroup_dvd_card
    rw [IsCyclic.card_mulAut, hHcard] at hdvd
    norm_num at hdvd ⊢
    exact hdvd
  have hφrange : Nat.card φ.range = 1 := by
    apply Nat.dvd_one.mp
    simpa using Nat.dvd_gcd hφrange_dvd3 hφrange_dvd64
  have hφ : φ = 1 := by
    rw [← φ.range_eq_bot_iff]
    exact φ.range.eq_bot_iff_card.mpr hφrange
  have e := SemidirectProduct.mulEquivSubgroup hcomp
  rw [show H.normalizerMonoidHom.comp
      (Subgroup.inclusion (H.normalizer_eq_top ▸ le_top)) = 1 from hφ] at e
  apply e.isCyclic.mp
  apply SemidirectProduct.mulEquivProd.isCyclic.mpr
  exact Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, by
    rw [hHcard, hPcard]
    norm_num⟩

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
    rcases apm_b01A02_exists_normal_card_85 G hGcard with
      ⟨H, P, hHnormal, hHcard, hPcard, hcomp⟩
    letI : Fintype H := Fintype.ofFinite H
    refine ⟨⟨H, hHnormal, hHcard,
      apm_b01A02_isCyclic_of_card_85 H hHcard⟩, ?_⟩
    exact apm_b01A02_isCyclic_of_card_255 G hGcard
#print axioms apm_b01a02

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

/-- A faithful action on a finite type of cardinality `n` gives the requested
embedding into the concretely indexed symmetric group `Sₙ`. -/
lemma apm_b93a01_embeds_fin_of_faithful_action
    (G α : Type) [Group G] [MulAction G α] [Fintype α] (n : ℕ)
    (hcard : Fintype.card α = n)
    (hinj : Function.Injective (MulAction.toPermHom G α)) :
    apm_b93a01_embeds G (Equiv.Perm (Fin n)) := by
  classical
  let e : α ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G α), ?_⟩
  exact e.permCongrHom.injective.comp hinj

lemma apm_b93a01_abelian_of_normal_prime_factors
    (G : Type) [Group G] [Fintype G] (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Fintype.card G = p * q)
    (P Q : Subgroup G) (hPn : P.Normal) (hQn : Q.Normal)
    (hPcard : Nat.card P = p) (hQcard : Nat.card Q = q) :
    ∀ a b : G, a * b = b * a := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  letI : IsCyclic P := isCyclic_of_prime_card hPcard
  letI : IsCyclic Q := isCyclic_of_prime_card hQcard
  have hpne : p ≠ q := ne_of_lt hpq
  have hcop : (Nat.card P).Coprime (Nat.card Q) := by
    rw [hPcard, hQcard]
    exact (Nat.coprime_primes hp hq).2 hpne
  have hmul : Nat.card P * Nat.card Q = Nat.card G := by
    rw [hPcard, hQcard, Nat.card_eq_fintype_card, hcard]
  have hcomp : P.IsComplement' Q :=
    Subgroup.isComplement'_of_coprime hmul hcop
  intro a b
  obtain ⟨⟨aP, aQ⟩, rfl⟩ := hcomp.2 a
  obtain ⟨⟨bP, bQ⟩, rfl⟩ := hcomp.2 b
  have haQbP : Commute (aQ : G) (bP : G) :=
    Subgroup.commute_of_normal_of_disjoint Q P hQn hPn hcomp.disjoint.symm
      aQ bP aQ.property bP.property
  have haPbP : (aP : G) * bP = bP * aP :=
    congrArg Subtype.val (IsCyclic.commutative.comm aP bP)
  have haQbQ : (aQ : G) * bQ = bQ * aQ :=
    congrArg Subtype.val (IsCyclic.commutative.comm aQ bQ)
  have hbQaP : Commute (bQ : G) (aP : G) :=
    Subgroup.commute_of_normal_of_disjoint Q P hQn hPn hcomp.disjoint.symm
      bQ aP bQ.property aP.property
  calc
    ((aP : G) * aQ) * ((bP : G) * bQ) =
        (aP : G) * ((aQ : G) * bP) * bQ := by simp only [mul_assoc]
    _ = (aP : G) * ((bP : G) * aQ) * bQ := by rw [haQbP.eq]
    _ = ((aP : G) * bP) * ((aQ : G) * bQ) := by simp only [mul_assoc]
    _ = ((bP : G) * aP) * ((bQ : G) * aQ) := by rw [haPbP, haQbQ]
    _ = (bP : G) * ((aP : G) * bQ) * aQ := by simp only [mul_assoc]
    _ = (bP : G) * ((bQ : G) * aP) * aQ := by rw [hbQaP.eq]
    _ = ((bP : G) * bQ) * ((aP : G) * aQ) := by simp only [mul_assoc]

/-- The core of a subgroup of prime cardinality is either trivial or the
whole subgroup.  This is the kernel dichotomy needed for the Sylow coset
action below. -/
lemma apm_b93a01_normalCore_eq_bot_or_eq_self_of_prime_card
    (G : Type) [Group G] (H : Subgroup G)
    (hprime : (Nat.card H).Prime) :
    H.normalCore = ⊥ ∨ H.normalCore = H := by
  letI : Fact (Nat.card H).Prime := ⟨hprime⟩
  rcases (H.normalCore.subgroupOf H).eq_bot_or_eq_top_of_prime_card with hk | hk
  · left
    rw [Subgroup.subgroupOf_eq_bot] at hk
    apply le_antisymm
    · intro x hx
      exact Disjoint.le_bot hk ⟨hx, H.normalCore_le hx⟩
    · exact bot_le
  · right
    exact le_antisymm H.normalCore_le (Subgroup.subgroupOf_eq_top.mp hk)

lemma apm_b93a01_prime_dvd_multiset_lcm
    (r : ℕ) (hr : r.Prime) (s : Multiset ℕ) (h : r ∣ s.lcm) :
    ∃ a ∈ s, r ∣ a := by
  induction s using Multiset.induction_on with
  | empty => exact (hr.not_dvd_one h).elim
  | @cons a s ih =>
      rw [Multiset.lcm_cons] at h
      rcases hr.dvd_or_dvd_of_dvd_lcm h with ha | hs
      · exact ⟨a, by simp, ha⟩
      · obtain ⟨b, hb, hrb⟩ := ih hs
        exact ⟨b, by simp [hb], hrb⟩

/-- A permutation of order `p*q` needs at least `p+q` points. -/
lemma apm_b93a01_card_le_of_perm_order_prime_mul
    {α : Type} [Fintype α] [DecidableEq α] (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (σ : Equiv.Perm α) (horder : orderOf σ = p * q) :
    p + q ≤ Fintype.card α := by
  have hplcm : p ∣ σ.cycleType.lcm := by
    rw [Equiv.Perm.lcm_cycleType, horder]
    exact dvd_mul_right p q
  have hqlcm : q ∣ σ.cycleType.lcm := by
    rw [Equiv.Perm.lcm_cycleType, horder]
    exact dvd_mul_left q p
  obtain ⟨a, ha, hpa⟩ := apm_b93a01_prime_dvd_multiset_lcm p hp _ hplcm
  obtain ⟨b, hb, hqb⟩ := apm_b93a01_prime_dvd_multiset_lcm q hq _ hqlcm
  have hadvd : a ∣ p * q := by
    rw [← horder, ← Equiv.Perm.lcm_cycleType]
    exact Multiset.dvd_lcm ha
  have hbdvd : b ∣ p * q := by
    rw [← horder, ← Equiv.Perm.lcm_cycleType]
    exact Multiset.dvd_lcm hb
  have hsum : p + q ≤ σ.cycleType.sum := by
    by_cases hab : a = b
    · subst b
      have hpq_dvd_a : p * q ∣ a := (Nat.coprime_primes hp hq |>.2
        (ne_of_lt hpq)).mul_dvd_of_dvd_of_dvd hpa hqb
      have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (mul_pos hp.pos hq.pos)
      have hpq_le_a := Nat.le_of_dvd ha_pos hpq_dvd_a
      exact (show p + q ≤ a by nlinarith [hp.two_le, hq.two_le]).trans
        (Multiset.le_sum_of_mem ha)
    · have hb' : b ∈ σ.cycleType.erase a :=
        (Multiset.mem_erase_of_ne (Ne.symm hab)).2 hb
      have hab_le : a + b ≤ σ.cycleType.sum := by
        rw [← Multiset.cons_erase ha, Multiset.sum_cons]
        exact Nat.add_le_add_left (Multiset.le_sum_of_mem hb') a
      have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (mul_pos hp.pos hq.pos)
      have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd (mul_pos hp.pos hq.pos)
      exact (Nat.add_le_add (Nat.le_of_dvd ha_pos hpa)
        (Nat.le_of_dvd hb_pos hqb)).trans hab_le
  rw [Equiv.Perm.sum_cycleType] at hsum
  exact hsum.trans σ.support.card_le_univ

lemma apm_b93a01_faithful_sum_coset_action
    (G : Type) [Group G] (P Q : Subgroup G) (hd : Disjoint P Q) :
    Function.Injective
      (MulAction.toPermHom G ((G ⧸ P) ⊕ (G ⧸ Q))) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro g hg
    have heq : MulAction.toPermHom G ((G ⧸ P) ⊕ (G ⧸ Q)) g = 1 :=
      MonoidHom.mem_ker.mp hg
    have hP := congrArg (fun e : Equiv.Perm ((G ⧸ P) ⊕ (G ⧸ Q)) =>
      e (Sum.inl (QuotientGroup.mk 1))) heq
    have hQ := congrArg (fun e : Equiv.Perm ((G ⧸ P) ⊕ (G ⧸ Q)) =>
      e (Sum.inr (QuotientGroup.mk 1))) heq
    change Sum.inl (g • QuotientGroup.mk 1) = Sum.inl (QuotientGroup.mk 1) at hP
    change Sum.inr (g • QuotientGroup.mk 1) = Sum.inr (QuotientGroup.mk 1) at hQ
    injection hP with hP
    injection hQ with hQ
    have hgP : g ∈ P := by
      simpa using (QuotientGroup.eq.1 hP)
    have hgQ : g ∈ Q := by
      simpa using (QuotientGroup.eq.1 hQ)
    exact hd.le_bot ⟨hgP, hgQ⟩
  · exact bot_le

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
  refine ⟨⟨(Qs : Subgroup G), hQnormal, hQcard⟩, ?_, ?_⟩
  · rintro ⟨P, hPnormal, hPcard⟩
    exact apm_b93a01_abelian_of_normal_prime_factors G p q hp hq hpq hcard
      P (Qs : Subgroup G) hPnormal hQnormal hPcard hQcard
  ·
    /- CLOSER HOP 3 boundary: the structural second conjunct is closed.
       `Subgroup.isComplement'_of_coprime` decomposes every element through
       the normal prime-order subgroups; `isCyclic_of_prime_card` makes each
       factor commutative, and `Subgroup.commute_of_normal_of_disjoint`
       commutes cross terms.

       The new compiled helper
       `apm_b93a01_embeds_fin_of_faithful_action` closes the previously open
       transport from a faithful action on an abstract finite type of
       cardinality `n` to the required `Equiv.Perm (Fin n)`, using
       `Fintype.equivFinOfCardEq` and `Equiv.permCongrHom`.

       The historical remaining gap contained the two permutation-degree
       branches. In the nonabelian branch, `Subgroup.normalCore_eq_ker`
       identifies the coset-action kernel; what remains is to prove the normal
       core of a non-normal p-Sylow is bottom. A renewed search found
       `Subgroup.eq_bot_or_eq_top_of_prime_card`; using it requires viewing the
       core as a subgroup of the p-Sylow, then transporting the top case back
       to normality in G. In the abelian branch, one must obtain a
       cyclic generator, construct disjoint p/q cycles in `Fin (p+q)`, and
       formalize the cycle-type support lower bound excluding `Fin (p+q-1)`.
       Searches of `LEMMA-INDEX.md`, the closed artifacts (including partial
       neighbors `b90A01` and `b98A01`),
       `ConstructionTargets/`, and `YoungL2.lean` found no packaged bridge. -/
    constructor
    · intro hnab
      let Ps : Sylow p G := Classical.choice inferInstance
      have hPcard : Nat.card (Ps : Subgroup G) = p := by
        rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard]
        rw [Nat.factorization_mul hp.ne_zero hq.ne_zero, hp.factorization,
          hq.factorization]
        simp [Nat.ne_of_lt hpq]
      have hPindex : (Ps : Subgroup G).index = q := by
        have hm := Subgroup.card_mul_index (Ps : Subgroup G)
        rw [hPcard, Nat.card_eq_fintype_card, hcard] at hm
        nlinarith [hp.two_le]
      have hPnonnormal : ¬(Ps : Subgroup G).Normal := by
        intro hPn
        exact hnab (apm_b93a01_abelian_of_normal_prime_factors G p q hp hq hpq
          hcard (Ps : Subgroup G) (Qs : Subgroup G) hPn hQnormal hPcard hQcard)
      have hcore : (Ps : Subgroup G).normalCore = ⊥ := by
        rcases apm_b93a01_normalCore_eq_bot_or_eq_self_of_prime_card G
            (Ps : Subgroup G) (hPcard.symm ▸ hp) with hbot | hself
        · exact hbot
        · exact False.elim (hPnonnormal (hself ▸ inferInstance))
      let P : Subgroup G := Ps
      letI : Fintype (G ⧸ P) := Fintype.ofFinite (G ⧸ P)
      have hquotcard : Fintype.card (G ⧸ P) = q := by
        rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hPindex]
      constructor
      · apply apm_b93a01_embeds_fin_of_faithful_action G (G ⧸ P) q hquotcard
        rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
        exact hcore
      · exact hnoSmallNonabelian
    ·
      intro hab
      let Ps : Sylow p G := Classical.choice inferInstance
      have hPcard : Nat.card (Ps : Subgroup G) = p := by
        rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard]
        rw [Nat.factorization_mul hp.ne_zero hq.ne_zero, hp.factorization,
          hq.factorization]
        simp [Nat.ne_of_lt hpq]
      have hPindex : (Ps : Subgroup G).index = q := by
        have hm := Subgroup.card_mul_index (Ps : Subgroup G)
        rw [hPcard, Nat.card_eq_fintype_card, hcard] at hm
        nlinarith [hp.two_le]
      have hcomp : (Ps : Subgroup G).IsComplement' (Qs : Subgroup G) := by
        apply Subgroup.isComplement'_of_coprime
        · rw [hPcard, hQcard, Nat.card_eq_fintype_card, hcard]
        · rw [hPcard, hQcard]
          exact (Nat.coprime_primes hp hq).2 (ne_of_lt hpq)
      constructor
      · letI : Fintype (G ⧸ (Ps : Subgroup G)) := Fintype.ofFinite _
        letI : Fintype (G ⧸ (Qs : Subgroup G)) := Fintype.ofFinite _
        have hcP : Fintype.card (G ⧸ (Ps : Subgroup G)) = q := by
          rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hPindex]
        have hcQ : Fintype.card (G ⧸ (Qs : Subgroup G)) = p := by
          rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hQindex]
        have hsumcard : Fintype.card ((G ⧸ (Ps : Subgroup G)) ⊕
            (G ⧸ (Qs : Subgroup G))) = p + q := by
          rw [Fintype.card_sum, hcP, hcQ, add_comm]
        apply apm_b93a01_embeds_fin_of_faithful_action G _ (p + q) hsumcard
        exact apm_b93a01_faithful_sum_coset_action G _ _ hcomp.disjoint
      · rintro ⟨f, hf⟩
        letI : IsCyclic (Ps : Subgroup G) := isCyclic_of_prime_card hPcard
        letI : IsCyclic (Qs : Subgroup G) := isCyclic_of_prime_card hQcard
        obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Ps : Subgroup G))
        obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Qs : Subgroup G))
        have hxy : Commute (x : G) (y : G) := by
          exact hab (x : G) (y : G)
        obtain ⟨z, -, hz⟩ := hxy.exists_orderOf_eq_lcm
        have hzpq : orderOf z = p * q := by
          rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx, hy, hPcard, hQcard,
            Nat.lcm_eq_mul_div, Nat.Coprime.gcd_eq_one
            ((Nat.coprime_primes hp hq).2 (ne_of_lt hpq)), Nat.div_one] at hz
          exact hz
        have hforder : orderOf (f z) = p * q := (orderOf_injective f hf z).trans hzpq
        have hle := apm_b93a01_card_le_of_perm_order_prime_mul p q hp hq hpq
          (f z) hforder
        simp only [Fintype.card_fin] at hle
        omega

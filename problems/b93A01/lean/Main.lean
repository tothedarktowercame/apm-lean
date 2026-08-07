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

       The sole remaining sorry still contains the two permutation-degree
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
    sorry

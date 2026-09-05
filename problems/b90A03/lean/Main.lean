import Mathlib

/-!
# APM b90A03: Sylow subgroups and intermediate fields

## Statement repairs

Part (b) asks whether `L` is a Galois extension of `L`, which is always true.
We replace the second `L` by `K`: the intended conclusion is that `L/K` is
Galois, as confirmed by the supplied solution and the Galois correspondence.

## Encoding questions

None. Intermediate fields are represented by `IntermediateField K F`, and
`[F : L]` by `Module.finrank (↥L) F`.
-/

open Set

noncomputable section

/-- The `p`-part of the degree in the problem has the advertised exponent. -/
lemma apm_b90a03_factorization
    (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p ^ n * q ^ m).factorization p = n := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Finsupp.add_apply, hp.factorization_pow, hq.factorization_pow]
  simp [hpq]

/-- Every Sylow `p`-subgroup of the Galois group has order `p ^ n`. -/
lemma apm_b90a03_sylow_card
    (K F : Type) [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdegree : Module.finrank K F = p ^ n * q ^ m)
    (P : Sylow p Gal(F/K)) : Nat.card P = p ^ n := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Sylow.card_eq_multiplicity, IsGalois.card_aut_eq_finrank K F, hdegree,
    apm_b90a03_factorization p q n m hp hq hpq]

/-- A Sylow `p`-subgroup supplies the required proper intermediate field. -/
lemma apm_b90a03_exists_intermediateField
    (K F : Type) [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : 1 < n) (hm : 1 < m)
    (hdegree : Module.finrank K F = p ^ n * q ^ m) :
    ∃ L : IntermediateField K F,
      L ≠ ⊥ ∧ L ≠ ⊤ ∧ Module.finrank (↥L) F = p ^ n := by
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p Gal(F/K) := default
  let L : IntermediateField K F := IntermediateField.fixedField (P : Subgroup Gal(F/K))
  have hfin : Module.finrank (↥L) F = p ^ n := by
    rw [IntermediateField.finrank_fixedField_eq_card]
    exact apm_b90a03_sylow_card K F p q n m hp hq hpq hdegree P
  refine ⟨L, ?_, ?_, hfin⟩
  · intro hbot
    have htotal : Module.finrank K F = p ^ n := by
      rw [← hfin]
      have htower := Module.finrank_mul_finrank K (↥L) F
      rw [hbot, IntermediateField.finrank_bot, one_mul] at htower
      exact htower.symm.trans
        (congrArg (fun T : IntermediateField K F => Module.finrank (↥T) F)
          hbot).symm
    rw [hdegree] at htotal
    have hpn_pos : 0 < p ^ n := pow_pos hp.pos n
    have hqm_one : 1 < q ^ m := by
      exact one_lt_pow₀ hq.one_lt (by omega)
    nlinarith
  · intro htop
    have hone := hfin
    rw [htop, IntermediateField.finrank_top] at hone
    have hpn_one : 1 < p ^ n := one_lt_pow₀ hp.one_lt (by omega)
    omega

/-- Literal singleton equality transports to equality of the fixed fields of
all Sylow subgroups.  This is the set-extensionality step left implicit in the
previous hop. -/
lemma apm_b90a03_fixedField_eq_of_degree_singleton
    (K F : Type) [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hdegree : Module.finrank K F = p ^ n * q ^ m)
    (L : IntermediateField K F)
    (hunique : ({L' : IntermediateField K F |
        Module.finrank (↥L') F = p ^ n} : Set (IntermediateField K F)) = {L})
    (P : Sylow p Gal(F/K)) :
    IntermediateField.fixedField (P : Subgroup Gal(F/K)) = L := by
  have hmem : IntermediateField.fixedField (P : Subgroup Gal(F/K)) ∈
      ({L' : IntermediateField K F |
        Module.finrank (↥L') F = p ^ n} : Set (IntermediateField K F)) := by
    rw [Set.mem_setOf_eq, IntermediateField.finrank_fixedField_eq_card]
    exact apm_b90a03_sylow_card K F p q n m hp hq hpq hdegree P
  rw [hunique] at hmem
  exact Set.mem_singleton_iff.mp hmem

theorem apm_b90a03
    (K F : Type) [Field K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F]
    (p q n m : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hn : 1 < n) (hm : 1 < m)
    (hdegree : Module.finrank K F = p ^ n * q ^ m) :
    (∃ L : IntermediateField K F,
      L ≠ ⊥ ∧ L ≠ ⊤ ∧ Module.finrank (↥L) F = p ^ n) ∧
    ∀ L : IntermediateField K F,
      L ≠ ⊥ → L ≠ ⊤ → Module.finrank (↥L) F = p ^ n →
      (({L' : IntermediateField K F |
          Module.finrank (↥L') F = p ^ n} : Set (IntermediateField K F)) =
          {L} ↔
        IsGalois K (↥L)) := by
  refine ⟨apm_b90a03_exists_intermediateField K F p q n m hp hq hpq hn hm hdegree, ?_⟩
  /- PASS-1 boundary (Codex, sustained desk research): Mathlib contains the
     conceptual correspondence, notably
     `IntermediateField.finrank_fixedField_eq_card`,
     `IntermediateField.fixingSubgroup_fixedField`,
     `IsGalois.fixedField_fixingSubgroup`,
     `InfiniteGalois.normal_iff_isGalois`, and
     `intermediateFieldEquivSubgroup`.  Its Sylow library supplies
     `Sylow.card_eq_multiplicity`, `Sylow.normal_of_subsingleton`,
     `Sylow.isPretransitive_of_finite`, and conjugacy/normalizer results.

     I also searched all closed problem artifacts, `LEMMA-INDEX.md`, every
     `ConstructionTargets/` module, `YoungL2.lean`, git history, and the nearby
     partial group/Galois artifacts `b01J03`, `b90A01`, `b93A01`, `b96A02`, and
     `b99A02`.  None packages the required restricted correspondence.

     Closer hop 1 closes the arithmetic bridge in the compiled lemmas
     `apm_b90a03_factorization` and `apm_b90a03_sylow_card`: every Sylow
     `p`-subgroup of `Gal(F/K)` has cardinality exactly `p ^ n`.  These reuse
     `Nat.Prime.factorization_pow`, `Sylow.card_eq_multiplicity`, and
     `IsGalois.card_aut_eq_finrank`.

     The remaining bridge must construct a Sylow subgroup's fixed field and
     prove both properness claims, then prove that every field
     of relative finrank `p ^ n` has fixing subgroup carrying the full p-part
     and hence is a Sylow subgroup.  Finally it must transport uniqueness as a
     literal set equality with `{L}` through the order-reversing Galois
     correspondence and identify Sylow uniqueness with normality before using
     `InfiniteGalois.normal_iff_isGalois`.  The individual APIs exist, but this
     subtype/set-extensionality development remains open; no unproved
     intermediate assertion was introduced.  The repaired frozen statement
     appears mathematically sound.

     Closer hop 2 closes the entire existential half in
     `apm_b90a03_exists_intermediateField`.  Taking the fixed field of any
     Sylow subgroup gives relative finrank `p^n` immediately from
     `IntermediateField.finrank_fixedField_eq_card`; the two strictness claims
     reduce to `p^n > 1`, `q^m > 1`, and the tower degree formula already
     present as `hdegree`.

     Closer hop 3 now compiles the first literal-set transport as
     `apm_b90a03_fixedField_eq_of_degree_singleton`: singleton equality forces
     the fixed field of every Sylow subgroup to equal `L`.  The remaining
     forward implication is to apply injectivity of the Galois correspondence
     to deduce that all Sylow subgroups equal `L.fixingSubgroup`, hence that it
     is normal.  The reverse implication requires installing the `Unique`
     Sylow instance from normality and transporting it back to the literal set
     equality. Searches of the correspondence, `OrderIso` image/preimage, and
     Sylow uniqueness APIs found no declaration packaging this restricted
     singleton equivalence. -/

  intro L hne_bot hne_top hfinL
  letI : Fact p.Prime := ⟨hp⟩
  have hcardG : Nat.card Gal(F/K) = p ^ n * q ^ m :=
    (IsGalois.card_aut_eq_finrank K F).trans hdegree
  have hcardH : Nat.card L.fixingSubgroup = p ^ n := by
    rw [← IntermediateField.finrank_fixedField_eq_card,
      IsGalois.fixedField_fixingSubgroup L]
    exact hfinL
  have hcardS : Nat.card L.fixingSubgroup = p ^ (Nat.card Gal(F/K)).factorization p := by
    rw [hcardH, hcardG, apm_b90a03_factorization p q n m hp hq hpq]
  constructor
  · -- Forward: literal set equality {L'}-singleton forces IsGalois K L
    intro hset
    have hfixall : ∀ Q : Sylow p Gal(F/K),
        IntermediateField.fixedField (Q : Subgroup Gal(F/K)) = L :=
      fun Q => apm_b90a03_fixedField_eq_of_degree_singleton K F p q n m hp hq hpq
        hdegree L hset Q
    have hcoe : ∀ Q : Sylow p Gal(F/K),
        (Q : Subgroup Gal(F/K)) = L.fixingSubgroup := by
      intro Q
      calc (Q : Subgroup Gal(F/K))
          = IntermediateField.fixingSubgroup
              (IntermediateField.fixedField (Q : Subgroup Gal(F/K))) :=
            (IntermediateField.fixingSubgroup_fixedField
              (F := K) (E := F) (H := (Q : Subgroup Gal(F/K)))).symm
        _ = L.fixingSubgroup := by rw [hfixall Q]
    haveI hsub : Subsingleton (Sylow p Gal(F/K)) :=
      ⟨fun Q Q' => Sylow.ext ((hcoe Q).trans (hcoe Q').symm)⟩
    have hnorm : (default : Sylow p Gal(F/K)).Normal :=
      Sylow.normal_of_subsingleton _
    have hnorm' : L.fixingSubgroup.Normal := by
      rw [← hcoe default]; exact hnorm
    exact (InfiniteGalois.normal_iff_isGalois L).mp hnorm'
  · -- Reverse: IsGalois K L forces the literal set equality
    intro hgalois
    have huniq : Unique (Sylow p Gal(F/K)) := by
      refine Sylow.unique_of_normal (Sylow.ofCard L.fixingSubgroup hcardS) ?_
      show ((Sylow.ofCard L.fixingSubgroup hcardS : Sylow p Gal(F/K)) :
          Subgroup Gal(F/K)).Normal
      rw [Sylow.coe_ofCard]
      exact IsGalois.fixingSubgroup_normal_of_isGalois L
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · rw [Set.mem_setOf_eq]; exact hfinL
    · intro L' hL'
      have hcardH' : Nat.card L'.fixingSubgroup = p ^ n := by
        rw [← IntermediateField.finrank_fixedField_eq_card,
          IsGalois.fixedField_fixingSubgroup L']
        exact hL'
      have hcardS' : Nat.card L'.fixingSubgroup
          = p ^ (Nat.card Gal(F/K)).factorization p := by
        rw [hcardH', hcardG, apm_b90a03_factorization p q n m hp hq hpq]
      have hQ : (Sylow.ofCard L'.fixingSubgroup hcardS' : Sylow p Gal(F/K))
          = Sylow.ofCard L.fixingSubgroup hcardS :=
        Subsingleton.elim _ _
      have hQcoe : (Sylow.ofCard L'.fixingSubgroup hcardS' : Subgroup Gal(F/K))
          = L'.fixingSubgroup := Sylow.coe_ofCard _ _
      rw [Sylow.ext_iff] at hQ
      have hL'eq : L' = IntermediateField.fixedField (L'.fixingSubgroup) :=
        (IsGalois.fixedField_fixingSubgroup L').symm
      have hLeq : IntermediateField.fixedField (L.fixingSubgroup) = L :=
        IsGalois.fixedField_fixingSubgroup L
      calc L' = IntermediateField.fixedField (L'.fixingSubgroup) := hL'eq
        _ = IntermediateField.fixedField (L.fixingSubgroup) := by
            rw [← hQcoe, ← Sylow.coe_ofCard L.fixingSubgroup hcardS, ← hQ]
        _ = L := hLeq


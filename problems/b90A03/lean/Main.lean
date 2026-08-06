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

     The remaining bridge must prove
       `(p ^ n * q ^ m).factorization p = n`
     from `hp`, `hq`, and `hpq`, rewrite the cardinal of an arbitrary Sylow
     subgroup using `Sylow.card_eq_multiplicity` and `hdegree`, construct its
     fixed field and prove both properness claims, then prove that every field
     of relative finrank `p ^ n` has fixing subgroup carrying the full p-part
     and hence is a Sylow subgroup.  Finally it must transport uniqueness as a
     literal set equality with `{L}` through the order-reversing Galois
     correspondence and identify Sylow uniqueness with normality before using
     `InfiniteGalois.normal_iff_isGalois`.  The individual APIs exist, but this
     subtype/cardinality/set-extensionality development was not completed
     within the 15--25 minute pass; no unproved intermediate assertion was
     introduced.  The repaired frozen statement appears mathematically sound. -/
  sorry

import Mathlib

/-!
# APM b96J04: Splitting fields of `X⁸ + 1`

## Statement repairs

None.

## Encoding questions

None. Both splitting fields are arbitrary field extensions satisfying
`Polynomial.IsSplittingField`. Degree-four subfields are counted as actual
intermediate fields, not replaced by their corresponding subgroups. The
`Fact (Nat.Prime 41)` parameter supplies Mathlib's field structure on `ZMod 41`.
-/

open Polynomial

noncomputable section

local instance apm_b96J04_fact_prime_41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩

def apm_b96J04_fQ : ℚ[X] := X ^ 8 + 1

def apm_b96J04_f41 : (ZMod 41)[X] := X ^ 8 + 1

/-- `X⁸+1` is exactly the sixteenth cyclotomic polynomial over any field. -/
lemma apm_b96J04_X_pow_eight_add_one_eq_cyclotomic
    (F : Type*) [Field F] :
    (X ^ 8 + 1 : F[X]) = cyclotomic 16 F := by
  rw [show (16 : ℕ) = 2 ^ (3 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num [Finset.sum_range_succ]
  ring

lemma apm_b96J04_fQ_eq_cyclotomic :
    apm_b96J04_fQ = cyclotomic 16 ℚ := by
  exact apm_b96J04_X_pow_eight_add_one_eq_cyclotomic ℚ

lemma apm_b96J04_f41_eq_cyclotomic :
    apm_b96J04_f41 = cyclotomic 16 (ZMod 41) := by
  exact apm_b96J04_X_pow_eight_add_one_eq_cyclotomic (ZMod 41)

/-- The Frobenius exponent `41` has order two modulo `16`. -/
lemma apm_b96J04_orderOf_41_mod_16 :
    orderOf (41 : ZMod 16) = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- The concrete unit group modulo `16` has eight elements. -/
lemma apm_b96J04_card_units_mod_16 : Nat.card (ZMod 16)ˣ = 8 := by
  rw [Nat.card_eq_fintype_card]
  native_decide

theorem apm_b96j04
    (K L : Type) [Field K] [Algebra ℚ K]
    [Fact (Nat.Prime 41)] [Field L] [Algebra (ZMod 41) L]
    [apm_b96J04_fQ.IsSplittingField ℚ K]
    [apm_b96J04_f41.IsSplittingField (ZMod 41) L] :
    Nonempty
      ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2 × ZMod 4)) ∧
    Nat.card
      {E : IntermediateField ℚ K // Module.finrank ℚ E = 4} = 3 ∧
    Nat.card
      {E : IntermediateField ℚ K //
        Module.finrank ℚ E = 4 ∧ IsGalois ℚ E} = 3 ∧
    Nonempty
      ((L ≃ₐ[ZMod 41] L) ≃* Multiplicative (ZMod 2)) := by
  /-
  PARTIAL boundary (closer hop 2): the polynomial identification is now
  compiled uniformly over every field as
  `apm_b96J04_X_pow_eight_add_one_eq_cyclotomic`, with specialized rewrite
  lemmas for both frozen base fields. Thus both arbitrary splitting-field
  instances can be rewritten literally as splitting fields of `cyclotomic 16`.

  Closer hop 2 compiles the concrete arithmetic on both sides of the missing
  transport. `apm_b96J04_orderOf_41_mod_16` proves that the Frobenius exponent
  has order exactly two, using `orderOf_eq_prime` and decidable arithmetic in
  `ZMod 16`. `apm_b96J04_card_units_mod_16` proves that `(ZMod 16)ˣ` has eight
  elements. A direct `native_decide` search cannot synthesize the requested
  structured group equivalence, and Mathlib's cyclotomic searches expose
  `IsCyclotomicExtension.finrank` over irreducible cyclotomic polynomials but
  no finite-field splitting-degree theorem consuming this order computation.

  The informal proof then uses the cyclotomic Galois-group
  isomorphism over `ℚ` and the Frobenius-order description over `ZMod 41`.
  Searches covered `Polynomial.IsSplittingField`,
  `FieldTheory.Galois.IsGaloisGroup`, `IntermediateField.finrank_fixedField_eq_card`,
  and Mathlib's cyclotomic files. The general Galois correspondence is present,
  but no compiled bridge was found that identifies `(K ≃ₐ[ℚ] K)` for this
  arbitrary splitting-field instance with `(ZMod 16)ˣ`, or identifies the
  finite-field splitting degree with the now-compiled value of
  `orderOf (41 : ZMod 16)`. Without those
  identifications, neither the automorphism-group conclusions nor the exact
  count of degree-four intermediate fields can be reached. No proof step
  compiled within the skip budget.
  -/
  sorry

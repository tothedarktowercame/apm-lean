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
  decide

def apm_b96J04_unitsCode (u : (ZMod 16)ˣ) :
    Multiplicative (ZMod 2 × ZMod 4) :=
  Multiplicative.ofAdd <| match u.1.val with
    | 1  => (0, 0)
    | 3  => (0, 1)
    | 9  => (0, 2)
    | 11 => (0, 3)
    | 15 => (1, 0)
    | 13 => (1, 1)
    | 7  => (1, 2)
    | 5  => (1, 3)
    | _  => (0, 0)

def apm_b96J04_unitsCodeHom :
    (ZMod 16)ˣ →* Multiplicative (ZMod 2 × ZMod 4) where
  toFun := apm_b96J04_unitsCode
  map_one' := by decide
  map_mul' := by decide

lemma apm_b96J04_units_mod_16_equiv :
    Nonempty ((ZMod 16)ˣ ≃* Multiplicative (ZMod 2 × ZMod 4)) := by
  exact ⟨MulEquiv.ofBijective apm_b96J04_unitsCodeHom (by decide)⟩

lemma apm_b96J04_isCyclotomicExtension_of_isSplittingField
    (K : Type*) [Field K] [Algebra ℚ K]
    [Polynomial.IsSplittingField ℚ K (cyclotomic 16 ℚ)] :
    IsCyclotomicExtension {16} ℚ K := by
  letI : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (16 : K) := ⟨Nat.cast_ne_zero.mpr (by norm_num)⟩
  rw [IsCyclotomicExtension.iff_singleton]
  obtain ⟨ζ, hζ⟩ := (Polynomial.IsSplittingField.splits K
    (cyclotomic 16 ℚ)).exists_eval_eq_zero
      (by simpa only [map_cyclotomic] using
        (degree_cyclotomic_pos 16 K (by norm_num)).ne')
  have hprim : IsPrimitiveRoot ζ 16 := by
    rw [← isRoot_cyclotomic_iff, IsRoot.def]
    simpa only [map_cyclotomic] using hζ
  refine ⟨⟨ζ, hprim⟩, ?_⟩
  have htop : Algebra.adjoin ℚ {b : K | b ^ 16 = 1} = ⊤ := by
    have heq :=
      IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots
        (A := ℚ) hprim
    simp only [Set.mem_singleton_iff, exists_eq_left, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, true_and] at heq
    rw [← heq]
    exact Polynomial.IsSplittingField.adjoin_rootSet K (cyclotomic 16 ℚ)
  exact Algebra.eq_top_iff.mp htop

/-- Once the abstract splitting field has been recognized as the sixteenth
cyclotomic extension, Mathlib's rational cyclotomic Galois equivalence applies
directly.  This packages both the automorphism-group model and its cardinality,
isolating recognition of the splitting field as the sole upstream bridge. -/
lemma apm_b96J04_aut_equiv_units_of_isCyclotomic
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {16} ℚ K] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 16)ˣ) ∧
      Nat.card (K ≃ₐ[ℚ] K) = 8 := by
  let e := IsCyclotomicExtension.Rat.galEquivZMod 16 K
  refine ⟨⟨e⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv, apm_b96J04_card_units_mod_16]

/-- The concrete unit-group equivalence completes the rational automorphism
group identification once the splitting field has been recognized as the
sixteenth cyclotomic extension. -/
lemma apm_b96J04_aut_equiv_product_of_isCyclotomic
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {16} ℚ K] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2 × ZMod 4)) := by
  obtain ⟨eunits⟩ := apm_b96J04_units_mod_16_equiv
  exact ⟨(IsCyclotomicExtension.Rat.galEquivZMod 16 K).trans eunits⟩

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
  elements. A direct computational search cannot synthesize the requested
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

  CLOSER HOP 3: `apm_b96J04_aut_equiv_units_of_isCyclotomic` now compiles the
  rational Galois transport after the precise missing recognition hypothesis.
  Given `IsCyclotomicExtension {16} ℚ K`, it applies
  `IsCyclotomicExtension.Rat.galEquivZMod` and obtains both the group
  equivalence `(K ≃ₐ[ℚ] K) ≃* (ZMod 16)ˣ` and cardinality eight, reusing the
  hop-2 unit-cardinality computation. Thus no further arbitrary-splitting-
  field transport is required after constructing that cyclotomic-extension
  instance.

  Searches beyond hop 2 covered the definition and singleton criteria for
  `IsCyclotomicExtension`, primitive-root/cyclotomic-root lemmas, rational
  `galEquivZMod`, and finite abelian group classification. They found no
  packaged conversion from `IsSplittingField ℚ K (cyclotomic 16 ℚ)` to the
  required cyclotomic-extension instance, nor a packaged structured
  equivalence `(ZMod 16)ˣ ≃* Multiplicative (ZMod 2 × ZMod 4)`. The finite-
  field Frobenius-degree bridge and subsequent subgroup enumeration also
  remain open.
  -/
  /-
  HOP 4 closes both identified rational-side holes.  The explicit computable
  homomorphism `apm_b96J04_unitsCodeHom` yields the requested structured unit
  equivalence, while
  `apm_b96J04_isCyclotomicExtension_of_isSplittingField` converts the literal
  cyclotomic splitting-field instance by comparing its root-set adjoin with
  the primitive-root adjoin characterization.  Their composite proves the
  rational automorphism-group conclusion in
  `apm_b96J04_aut_equiv_product_of_isCyclotomic`.  Applying that conclusion
  inside the frozen theorem still encounters its explicitly supplied
  rational `Algebra` instance versus `NumberField`'s canonical rational
  algebra, while the independent intermediate-field counts and finite-field
  Frobenius automorphism clause also remain open.
  -/
  sorry

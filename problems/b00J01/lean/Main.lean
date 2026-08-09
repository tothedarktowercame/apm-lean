import Mathlib

/-!
# APM b00J01

## Statement repairs

None.

## Encoding questions

None. Splitting fields are quantified abstractly via `IsSplittingField`, so the
answer is independent of the chosen construction. The six intermediate fields
over `ℚ` are described by their degrees, with the three cubic fields identified
exactly as the non-Galois ones.
-/

open Polynomial

/-- The polynomial `X³ - 7` over a field. -/
noncomputable def apm_b00j01_poly (F : Type*) [Field F] : Polynomial F :=
  X ^ 3 - C 7

local instance apm_b00j01_fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The concrete cubic-residue calculation underlying the finite-field part. -/
lemma apm_b00j01_seven_not_cube_mod13 :
    ∀ x : ZMod 13, x ^ 3 ≠ 7 := by
  native_decide

/-- Consequently `X³ - 7` has no root over `𝔽₁₃`. -/
lemma apm_b00j01_not_isRoot_mod13 (x : ZMod 13) :
    ¬IsRoot (apm_b00j01_poly (ZMod 13)) x := by
  simp only [IsRoot, apm_b00j01_poly, eval_sub, eval_pow, eval_X, eval_C]
  exact sub_ne_zero.mpr (apm_b00j01_seven_not_cube_mod13 x)

/-- The polynomial defining the finite-field splitting field is irreducible. -/
lemma apm_b00j01_irreducible_mod13 :
    Irreducible (apm_b00j01_poly (ZMod 13)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · norm_num [apm_b00j01_poly]
  · exact apm_b00j01_not_isRoot_mod13

lemma apm_b00j01_separable_mod13 :
    (apm_b00j01_poly (ZMod 13)).Separable :=
  PerfectField.separable_of_irreducible apm_b00j01_irreducible_mod13

lemma apm_b00j01_finiteField_isGalois
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    IsGalois (ZMod 13) M := by
  letI : FiniteDimensional (ZMod 13) M :=
    IsSplittingField.finiteDimensional M (apm_b00j01_poly (ZMod 13))
  exact IsGalois.of_separable_splitting_field apm_b00j01_separable_mod13

lemma apm_b00j01_finiteField_card_aut
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    Nat.card (M ≃ₐ[ZMod 13] M) = Module.finrank (ZMod 13) M := by
  letI : FiniteDimensional (ZMod 13) M :=
    IsSplittingField.finiteDimensional M (apm_b00j01_poly (ZMod 13))
  letI : IsGalois (ZMod 13) M := apm_b00j01_finiteField_isGalois M
  exact IsGalois.card_aut_eq_finrank (ZMod 13) M

/-- Irreducibility already forces the arbitrary splitting field's degree to
be a multiple of three.  This is the exact lower-degree constraint needed
before identifying it with the canonical degree-three Galois field. -/
lemma apm_b00j01_three_dvd_finiteField_finrank
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    3 ∣ Module.finrank (ZMod 13) M := by
  have hdvd := apm_b00j01_irreducible_mod13.natDegree_dvd_finrank
    (Polynomial.IsSplittingField.splits M (apm_b00j01_poly (ZMod 13)))
  norm_num [apm_b00j01_poly] at hdvd ⊢
  exact hdvd

/-- Consequently the automorphism group of the finite-field splitting field
has cardinality divisible by three. -/
lemma apm_b00j01_three_dvd_finiteField_card_aut
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    3 ∣ Nat.card (M ≃ₐ[ZMod 13] M) := by
  rw [apm_b00j01_finiteField_card_aut M]
  exact apm_b00j01_three_dvd_finiteField_finrank M

/-- Why this unblocks the rational-field conjunct of `apm_b00j01`: it is the
missing concrete Galois-correspondence computation for the splitting field of
`X³ - 7`, including the exhaustive list of intermediate fields and their
Galois status. -/
theorem apm_b00J01_bridge_1
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (apm_b00j01_poly ℚ)] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ (E₂ : IntermediateField ℚ K) (E₃ : Fin 3 → IntermediateField ℚ K),
        Module.finrank ℚ E₂ = 2 ∧
        Function.Injective E₃ ∧
        (∀ i, Module.finrank ℚ (E₃ i) = 3) ∧
        (∀ E : IntermediateField ℚ K,
          E = ⊥ ∨ E = E₂ ∨ (∃ i, E = E₃ i) ∨ E = ⊤) ∧
        IsGalois ℚ E₂ ∧
        (∀ i, ¬IsGalois ℚ (E₃ i)) := by
  sorry

/-- Why this unblocks the real-field conjunct of `apm_b00j01`: it identifies
the real splitting field as the quadratic extension obtained by adjoining a
nonreal root and computes its two-element automorphism group. -/
theorem apm_b00J01_bridge_2
    (L : Type*) [Field L] [Algebra ℝ L]
    [IsSplittingField ℝ L (apm_b00j01_poly ℝ)] :
    Nonempty ((L ≃ₐ[ℝ] L) ≃* Multiplicative (ZMod 2)) := by
  sorry

/-- Why this unblocks the finite-field conjunct of `apm_b00j01`: the exact
degree says that an irreducible cubic's root field already contains all three
roots, and the second conjunct transports the canonical degree-three
finite-field Frobenius action to the arbitrary splitting field. -/
theorem apm_b00J01_bridge_3
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    Module.finrank (ZMod 13) M = 3 ∧
      Nonempty ((M ≃ₐ[ZMod 13] M) ≃* Multiplicative (ZMod 3)) := by
  sorry

theorem apm_b00j01 :
    (∀ (K : Type*) [Field K] [Algebra ℚ K]
        [IsSplittingField ℚ K (apm_b00j01_poly ℚ)],
      Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ (E₂ : IntermediateField ℚ K) (E₃ : Fin 3 → IntermediateField ℚ K),
        Module.finrank ℚ E₂ = 2 ∧
        Function.Injective E₃ ∧
        (∀ i, Module.finrank ℚ (E₃ i) = 3) ∧
        (∀ E : IntermediateField ℚ K,
          E = ⊥ ∨ E = E₂ ∨ (∃ i, E = E₃ i) ∨ E = ⊤) ∧
        IsGalois ℚ E₂ ∧
        (∀ i, ¬IsGalois ℚ (E₃ i))) ∧
    (∀ (L : Type*) [Field L] [Algebra ℝ L]
        [IsSplittingField ℝ L (apm_b00j01_poly ℝ)],
      Nonempty ((L ≃ₐ[ℝ] L) ≃* Multiplicative (ZMod 2))) ∧
    (∀ [Fact (Nat.Prime 13)] (M : Type*) [Field M] [Algebra (ZMod 13) M]
        [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))],
      Nonempty ((M ≃ₐ[ZMod 13] M) ≃* Multiplicative (ZMod 3))) := by
  /-
  PARTIAL boundary (closer hop 3). This hop applies the general theorem
  `Polynomial.Irreducible.natDegree_dvd_finrank` to the arbitrary splitting
  field.  The compiled helpers
  `apm_b00j01_three_dvd_finiteField_finrank` and
  `apm_b00j01_three_dvd_finiteField_card_aut` prove respectively that its
  degree and its Galois automorphism-group cardinality are divisible by three.
  Thus the lower-bound half of the exact degree-three calculation is closed.

  Source inspection found `IsSplittingField.algEquiv`, which identifies two
  splitting fields of the *same polynomial*, and the canonical
  `GaloisField 13 3`, which is presented instead as a splitting field of
  `X^(13^3)-X`.  No theorem in the finite-field or splitting-field APIs shows
  directly that the roots of this particular irreducible cubic all lie in the
  degree-three root field, so the needed upper bound `finrank ≤ 3` and the
  transport to the canonical Frobenius equivalence remain open.

  The real splitting-field identification and the much larger rational `S₃`
  Galois-correspondence enumeration also remain open. Searches included
  `LEMMA-INDEX.md`, all construction targets, splitting-field uniqueness,
  finite Galois fields, cubic minpolys, and prior Galois siblings; none packages
  either classification required by the frozen conjunction.
  -/
  sorry

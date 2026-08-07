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
  PARTIAL boundary (closer hop 1): the finite-field arithmetic is now compiled.
  `apm_b00j01_seven_not_cube_mod13` exhausts `ZMod 13`, and
  `apm_b00j01_irreducible_mod13` packages the result as irreducibility of
  `X³ - 7`. This also corrects the original skip comment: the polynomial has
  no root over `𝔽₁₃`, rather than one root.

  Mathlib's `FieldTheory/Finite/GaloisField.lean` constructs and computes the
  canonical fields splitting `X^(p^n)-X`, but the frozen quantifier supplies an
  arbitrary splitting field of this cubic. The remaining finite-field bridge
  is transporting its degree-three irreducibility/splitting data to the
  canonical `GaloisField 13 3`, then transporting the Frobenius automorphism
  equivalence. The real splitting-field identification and the substantially
  larger rational `S₃` Galois-correspondence enumeration remain open.
  -/
  sorry

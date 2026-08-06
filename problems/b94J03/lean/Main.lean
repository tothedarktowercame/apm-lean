import Mathlib

/-!
# APM b94J03

## Statement repairs

None.

## Encoding questions

Splitting fields are quantified abstractly through `IsSplittingField`, so the
statement is independent of a chosen construction. They are described by their
base-field degree and Galois group; over `ℝ` the splitting field is additionally
identified with `ℂ`, and over `ZMod 7` its cardinality is identified as `343`.
-/

open Polynomial

/-- The polynomial `X³ - 3` over a field. -/
noncomputable def apm_b94J03_poly (F : Type*) [Field F] : Polynomial F :=
  X ^ 3 - C 3

theorem apm_b94j03 :
    (∀ (K : Type*) [Field K] [Algebra ℚ K]
      [IsSplittingField ℚ K (apm_b94J03_poly ℚ)],
      Module.finrank ℚ K = 6 ∧
        Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3))) ∧
    (∀ (K : Type*) [Field K] [Algebra ℝ K]
      [IsSplittingField ℝ K (apm_b94J03_poly ℝ)],
      Nonempty (K ≃ₐ[ℝ] ℂ) ∧
        Nonempty ((K ≃ₐ[ℝ] K) ≃* Multiplicative (ZMod 2))) ∧
    (∀ [Fact (Nat.Prime 7)] (K : Type*) [Field K] [Algebra (ZMod 7) K]
      [IsSplittingField (ZMod 7) K (apm_b94J03_poly (ZMod 7))],
        Module.finrank (ZMod 7) K = 3 ∧
        Nat.card K = 343 ∧
        Nonempty ((K ≃ₐ[ZMod 7] K) ≃* Multiplicative (ZMod 3))) := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hnoncube7 : ∀ a : ZMod 7, a ^ 3 ≠ 3 := by native_decide
  have hirr7 : Irreducible (apm_b94J03_poly (ZMod 7)) := by
    rw [apm_b94J03_poly]
    exact (X_pow_sub_C_irreducible_iff_of_prime (by norm_num : Nat.Prime 3)).2 hnoncube7
  -- (Sibling: b03J04)
  /- PASS-1 boundary: `hnoncube7` and `hirr7` now formally prove the key
     finite-field input: `3` is not a cube modulo `7`, hence `X³ - 3` is
     irreducible over `ZMod 7`.  This uses
     `X_pow_sub_C_irreducible_iff_of_prime`.  I searched
     `IsSplittingField.adjoin_rootSet`,
     `IsGalois.of_separable_splitting_field`, the irreducible-cubic and
     Eisenstein APIs, finite-field cardinality/finrank results, and the
     cyclicity of finite-field Galois groups.  The reusable solved artifact
     `b03J04` supplies general root-set/adjoin splitting-field machinery, but
     not the concrete degree or automorphism computations required here.
     I also inspected analogous artifact `b00J01`, but it is skipped rather
     than a solved sibling and is therefore not cited.  The intended proof must separately
     realize the abstract splitting fields as `ℚ(∛3, ζ₃)`, `ℂ` over `ℝ`, and
     the degree-three extension of `ZMod 7`, including the explicit
     root-of-unity computations.  I could not connect
     those realizations to the exact finrank, cardinality, and bundled
     `MulEquiv` conclusions within pass 1. -/
  sorry

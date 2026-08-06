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
  /- PASS-1 boundary: searched `IsSplittingField.adjoin_rootSet`,
     `IsGalois.of_separable_splitting_field`, the irreducible-cubic and
     Eisenstein APIs, finite-field cardinality/finrank results, and the
     cyclicity of finite-field Galois groups.  I also inspected the analogous
     repository artifact `b00J01`, but it is skipped rather than a solved
     sibling and is therefore not cited.  The intended proof must separately
     realize the abstract splitting fields as `ℚ(∛3, ζ₃)`, `ℂ` over `ℝ`, and
     the degree-three extension of `ZMod 7`, including the explicit
     irreducibility and root-of-unity computations.  I could not connect
     those realizations to the exact finrank, cardinality, and bundled
     `MulEquiv` conclusions within pass 1. -/
  sorry

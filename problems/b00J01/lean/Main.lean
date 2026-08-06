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
  -- SKIPPED: three-part Galois theory problem for x³-7 over ℚ, ℝ, F₁₃.
  -- (a) Over ℚ: Gal(K/ℚ) ≅ S₃, 6 intermediate fields, 3 cubic non-Galois.
  -- (b) Over ℝ: Gal(L/ℝ) ≅ Z₂ (complex conjugation).
  -- (c) Over F₁₃: Gal(M/F₁₃) ≅ Z₃ (Frobenius, since x³≡7 has one root mod 13
  --     and splitting field is F₁₃³).
  -- Blocker: requires assembling IsSplittingField, Galois group computation,
  -- IntermediateField enumeration, IsGalois — deep algebra infrastructure.
  -- APIs: `IsSplittingField`, `IntermediateField`, `IsGalois`, `AlgEquiv`
  sorry

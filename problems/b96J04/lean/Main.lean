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

def apm_b96J04_fQ : ℚ[X] := X ^ 8 + 1

def apm_b96J04_f41 : (ZMod 41)[X] := X ^ 8 + 1

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
  sorry

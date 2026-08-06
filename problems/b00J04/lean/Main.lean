import Mathlib

noncomputable section

/-!
# APM b00J04

## Statement repairs

None.

## Encoding notes

The inclusions `R ⊆ S ⊆ F` are represented by an intermediate
`Subalgebra R F`; its bottom element is precisely the embedded copy of `R`.
`IsFractionRing R F` records that `F` is the fraction field of `R`.
-/

theorem apm_b00j04
    (R F : Type*)
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Subalgebra R F) :
    (∀ α : S, ∃ a b : R, b ≠ 0 ∧
      (α : F) = algebraMap R F a / algebraMap R F b ∧
      (algebraMap R F b)⁻¹ ∈ S) ∧
    IsPrincipalIdealRing S ∧
    (Module.Finite R S → S = ⊥) := by
  sorry

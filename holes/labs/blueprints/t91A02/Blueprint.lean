import Mathlib
import ConstructionTargets.Surfaces

/-! # t91A02: Euler-characteristic obstruction to a surface cover

The sole missing foundation is multiplicativity of Euler characteristic for
the concrete finite-sheeted cover in the frozen statement.  Once supplied,
the contradiction is integer arithmetic.
-/

open ConstructionTargets.Surfaces

/-- **LIBRARY.** Euler characteristic is multiplicative for the finite cover
between the two concrete nonorientable polygon surfaces occurring in the
problem. -/
theorem t91A02_eulerCharacteristic_finite_cover
    (p : Surface false 16 → Surface false 8) (sheets : ℕ)
    (hp : IsCoveringMap p) (hsheets : 0 < sheets)
    (hfiber : ∀ x : Surface false 8,
      Nat.card {e : Surface false 16 // p e = x} = sheets) :
    eulerCharacteristic false 16 =
      (sheets : ℤ) * eulerCharacteristic false 8 := by
  sorry

theorem apm_t91a02 :
    ¬ ∃ (p : Surface false 16 → Surface false 8) (sheets : ℕ),
      IsCoveringMap p ∧ 0 < sheets ∧
      ∀ x : Surface false 8, Nat.card {e : Surface false 16 // p e = x} = sheets := by
  rintro ⟨p, sheets, hp, hsheets, hfiber⟩
  have heuler :=
    t91A02_eulerCharacteristic_finite_cover p sheets hp hsheets hfiber
  norm_num [eulerCharacteristic] at heuler
  omega

#print axioms apm_t91a02

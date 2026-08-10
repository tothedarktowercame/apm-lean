import Mathlib

/-!
# APM b00J02

## Statement repairs

None.

## Encoding questions

None. `GL (Fin 3) (ZMod 4)` is Mathlib's group of invertible `3 × 3`
matrices over `ℤ/4ℤ`.
-/

/-- The residue-field factor in the reduction-modulo-two count. -/
lemma apm_b00j02_card_GL_mod2 :
    Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field]
  decide

theorem apm_b00j02 :
    Fintype.card (GL (Fin 3) (ZMod 4)) = 86016 := by
  /-
  The remaining bridge is the reduction homomorphism
  `GeneralLinearGroup.map (ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2))`.
  One must prove it surjective and identify its kernel with the 512 matrices
  `1 + 2A`, `A : Matrix (Fin 3) (Fin 3) (ZMod 2)`.  Together with
  `apm_b00j02_card_GL_mod2`, the finite-group homomorphism cardinality formula
  gives `512 * 168 = 86016`.

  Mathlib provides `GeneralLinearGroup.map`, `ZMod.castHom_surjective`, and
  `Matrix.card_GL_field`, but no lifting theorem showing that a surjective
  ring homomorphism induces a surjection on `GL`, nor the square-zero-kernel
  count. Direct kernel `decide` was also tested: the default recursion limit
  fails, and raising it to 20,000 still fails (100,000 overflows the process
  stack), so kernel evaluation is not a viable axiom-clean route.
  -/
  sorry

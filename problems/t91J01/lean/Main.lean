import Mathlib

/-!
# APM t91J01

## Statement repairs

None.

## Encoding questions

None. The domain is Mathlib's standard ternary `cantorSet`, and the codomain
is the actual subtype of irrational real numbers strictly between `0` and `1`,
both carrying their subspace topologies.
-/

open Set

abbrev apm_t91J01_Cantor := cantorSet
abbrev apm_t91J01_IrrationalsInUnitInterval :=
  {x : ℝ // Irrational x ∧ 0 < x ∧ x < 1}

theorem apm_t91j01 :
    (¬∃ f : C(apm_t91J01_Cantor, apm_t91J01_IrrationalsInUnitInterval),
      Function.Surjective f) ∧
    ∃ f : C(apm_t91J01_Cantor, apm_t91J01_IrrationalsInUnitInterval),
      Function.Injective f := by
  sorry

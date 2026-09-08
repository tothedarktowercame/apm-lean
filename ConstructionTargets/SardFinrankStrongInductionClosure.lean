import Mathlib

namespace SardFinrankStrongInductionClosureProbe

/-- A source-dimension-indexed Sard property closes once every dimension is
proved from all strictly smaller dimensions. -/
theorem all_dimensions_of_strong_induction
    (P : ℕ → Prop)
    (hstep : ∀ d : ℕ, (∀ e : ℕ, e < d → P e) → P d) :
    ∀ d : ℕ, P d := by
  intro d
  exact Nat.strong_induction_on d hstep

#print axioms all_dimensions_of_strong_induction

end SardFinrankStrongInductionClosureProbe

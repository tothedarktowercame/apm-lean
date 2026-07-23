import Mathlib

noncomputable section

namespace ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1774994174583.Main

open scoped BigOperators

/-- Additive equivalence between `ZMod 1 × ZMod n` and `ZMod n`. -/
def zmodOneProdEquiv (n : ℕ) : (ZMod 1 × ZMod n) ≃+ ZMod n where
  toFun x := x.2
  invFun y := (0, y)
  left_inv x := by cases x; simp
  right_inv y := rfl
  map_add' x y := rfl

/-- Special case of part (b): when `m = 1`, the direct sum `Z/m ⊕ Z/n` is cyclic. -/
lemma zmod_one_prod_isCyclic (n : ℕ) :
    IsCyclic (ZMod 1 × ZMod n) := by
  classical
  simpa using (IsCyclic.ofAddEquiv (zmodOneProdEquiv n))

end ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1774994174583.Main

import Mathlib
import ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1775001319272.Scratch

noncomputable section

namespace ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1775001319272.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open scoped BigOperators

/-- Specialisation of Mathlib's instance saying that every finite subgroup of the units
of an integral domain is cyclic.  For a field `K`, any finite multiplicative subgroup is cyclic. -/
theorem finite_mul_subgroup_cyclic {K : Type*} [Field K] (G : Subgroup Kˣ) [Finite G] :
    IsCyclic G := by
  infer_instance

/-- The direct sum `ℤ / mℤ ⊕ ℤ / nℤ` (viewed additively as `ZMod m × ZMod n`) is cyclic iff
`m` and `n` are coprime. -/
theorem zmod_prod_cyclic_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsAddCyclic (ZMod m × ZMod n) ↔ Nat.Coprime m n := by
  classical
  refine (AddGroup.isAddCyclic_prod_iff (M := ZMod m) (N := ZMod n)).trans ?_
  have hreduce :
      (IsAddCyclic (ZMod m) ∧ IsAddCyclic (ZMod n) ∧
          (Nat.card (ZMod m)).Coprime (Nat.card (ZMod n))) ↔
        (Nat.card (ZMod m)).Coprime (Nat.card (ZMod n)) := by
    constructor
    · intro h
      exact h.2.2
    · intro h
      exact ⟨inferInstance, inferInstance, h⟩
  have hrewrite :
      (Nat.card (ZMod m)).Coprime (Nat.card (ZMod n)) ↔ Nat.Coprime m n := by
    simpa [Nat.card_zmod, hm, hn]
  exact hreduce.trans hrewrite

end ApmCanaries.Frames.B94J01.Apm_v2_b94J01_1775001319272.Main

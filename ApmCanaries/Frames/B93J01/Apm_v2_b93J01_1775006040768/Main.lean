import Mathlib
import ApmCanaries.Frames.B93J01.Apm_v2_b93J01_1775006040768.Scratch

noncomputable section

namespace ApmCanaries.Frames.B93J01.Apm_v2_b93J01_1775006040768.Main

open scoped BigOperators

/-!  Frame-local Lean witnesses for the algebra prelim problem b93J01. -/

namespace Examples

/-- The symmetric group on three letters has six elements. -/
lemma card_sym3 :
    Fintype.card (SymmetricGroup (Fin 3)) = 6 := by
  classical
  have hfact : (3)! = 6 := by decide
  simpa [SymmetricGroup, Fintype.card_perm, hfact]

/-- `S₃` is not commutative. -/
lemma sym3_not_isCommutative :
    ¬ IsCommutative (SymmetricGroup (Fin 3)) := by
  classical
  have hneq :
      ((Equiv.swap (0 : Fin 3) 1 : SymmetricGroup (Fin 3)) *
          Equiv.swap 1 2) ≠
        (Equiv.swap 1 2 *
          (Equiv.swap (0 : Fin 3) 1)) := by
    decide
  intro h
  exact hneq (h.comm _ _)

/-- `S₃` is not cyclic, hence furnishes the order-`pq` counterexample. -/
lemma sym3_not_isCyclic :
    ¬ IsCyclic (SymmetricGroup (Fin 3)) := by
  intro h
  exact sym3_not_isCommutative (IsCyclic.isCommutative h)

/-- The elementary abelian group `(Z/2Z)^3` has eight elements. -/
lemma card_zmod2_cubed :
    Fintype.card ((ZMod 2) × (ZMod 2) × (ZMod 2)) = 8 := by
  classical
  have : (Fintype.card (ZMod 2)) = 2 := by
    simpa using (ZMod.card 2)
  -- unfold the product cardinality step-by-step
  simpa [Fintype.card_prod, this, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

end Examples

end ApmCanaries.Frames.B93J01.Apm_v2_b93J01_1775006040768.Main

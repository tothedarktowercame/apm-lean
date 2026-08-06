import Mathlib

/-! # APM t93A03: a connected sum with nontrivial fundamental group

## Statement repairs

None.

## Encoding question

Mathlib has no connected-sum construction for smooth three-manifolds.  The
specific manifold `(S¹ × S²) # (S¹ × S²)` and its basepoint are therefore
retained as typed placeholders; its fundamental group is stated explicitly as
the free group on two generators.
-/

open FundamentalGroupoid

def t93A03ConnectedSum : TopCat := by sorry
def t93A03Basepoint : t93A03ConnectedSum := by sorry

theorem apm_t93a03 :
    Nonempty
      (FundamentalGroup t93A03ConnectedSum t93A03Basepoint ≃*
        FreeGroup (Fin 2)) ∧
    ¬SimplyConnectedSpace t93A03ConnectedSum := by
  sorry

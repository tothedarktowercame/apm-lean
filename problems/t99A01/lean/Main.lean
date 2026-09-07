import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! # APM t99A01: attaching cells of degrees 2, 4, and 5

## Statement repairs

Mathlib does not currently provide a CW-cell attachment construction together
with van Kampen and cellular-homology comparison theorems.  Accordingly, the
topological comparison step is NOT encoded.  The theorem records the two
algebraic calculations produced by those comparison theorems: the one-generator
presentations for the fundamental groups and the kernels of the cellular
boundary matrices.  `H₀ = ℤ`, the cokernel calculations for `H₁`, and vanishing
of higher cellular groups are omitted rather than represented by placeholders.

## Encoding questions

The single generator is indexed by `Unit`.  The cellular boundary maps are
written explicitly on `Fin 1`, `Fin 2`, and `Fin 3` tuples of integers.
-/

namespace APMT99A01

def rels (ds : Set ℕ) : Set (FreeGroup Unit) :=
  {w | ∃ d ∈ ds, w = (FreeGroup.of () : FreeGroup Unit) ^ d}

def boundaryX : (Fin 1 → ℤ) →+ ℤ where
  toFun v := 2 * v 0
  map_zero' := by simp
  map_add' := by intro x y; simp [mul_add]

def boundaryY : (Fin 2 → ℤ) →+ ℤ where
  toFun v := 2 * v 0 + 4 * v 1
  map_zero' := by simp
  map_add' := by intro x y; simp [mul_add, add_assoc, add_left_comm]

def boundaryZ : (Fin 3 → ℤ) →+ ℤ where
  toFun v := 2 * v 0 + 4 * v 1 + 5 * v 2
  map_zero' := by simp
  map_add' := by intro x y; simp [mul_add, add_assoc, add_left_comm]

end APMT99A01

theorem apm_t99a01 :
    Nonempty (PresentedGroup (APMT99A01.rels {2}) ≃* Multiplicative (ZMod 2)) ∧
    Nonempty (PresentedGroup (APMT99A01.rels {2, 4}) ≃* Multiplicative (ZMod 2)) ∧
    Subsingleton (PresentedGroup (APMT99A01.rels {2, 4, 5})) ∧
    Nonempty (AddMonoidHom.ker APMT99A01.boundaryX ≃+ (Fin 0 → ℤ)) ∧
    Nonempty (AddMonoidHom.ker APMT99A01.boundaryY ≃+ ℤ) ∧
    Nonempty (AddMonoidHom.ker APMT99A01.boundaryZ ≃+ (Fin 2 → ℤ)) := by
  sorry

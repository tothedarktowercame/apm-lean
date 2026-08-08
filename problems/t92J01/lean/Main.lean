import Mathlib

/-!
# APM t92J01 — a union of connected sets with a common point

The family is represented by a function `C : A → Set X`, and its union by
`⋃ a, C a`.  The shared point occurs explicitly in every member.

## Statement repairs

The index type is required to be nonempty.  Without this condition the
hypothesis that every member contains `x` is vacuous, the union is empty, and
Mathlib's `IsConnected` conclusion is false because it includes nonemptiness.

## Encoding questions

None.
-/

theorem apm_t92j01
    {A X : Type*} [Nonempty A] [TopologicalSpace X]
    {C : A → Set X} {x : X}
    (hConn : ∀ a, IsConnected (C a))
    (hx : ∀ a, x ∈ C a) :
    IsConnected (⋃ a, C a) := by
  sorry

import Mathlib

/-!
# APM t93J02 — nested intersections of compact connected sets

## Statement repairs

None. The sequence beginning at one in the source is harmlessly reindexed by
Lean's natural numbers beginning at zero.

## Encoding questions

None.
-/

open Set

noncomputable section

theorem apm_t93j02 {Y : Type} [TopologicalSpace Y] [T2Space Y]
    (C : ℕ → Set Y)
    (hcompact : ∀ n, IsCompact (C n))
    (hconn : ∀ n, IsConnected (C n))
    (hclosed : ∀ n, IsClosed (C n))
    (hsubset : ∀ n, C (n + 1) ⊆ C n)
    (hne : ∀ n, (C n).Nonempty) :
    IsCompact (⋂ n, C n) ∧ IsConnected (⋂ n, C n) := by
  sorry

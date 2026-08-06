import Mathlib

/-! # APM t95J01: Hausdorffness under a perfect surjection

## Statement repairs

The phrase “`π⁻¹` is compact for all `y`” is read as “the fiber
`π⁻¹({y})` is compact for every `y`”; an inverse map need not exist.
-/

open Set

theorem apm_t95j01
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (π : X → Y) (hcont : Continuous π) (hsurj : Function.Surjective π)
    (hclosed : IsClosedMap π)
    (hcompact : ∀ y : Y, IsCompact (π ⁻¹' ({y} : Set Y))) :
    T2Space Y := by
  sorry

import Mathlib

/-! # APM tunk02: products of regular spaces

## Statement repairs

None.

## Encoding questions

Regularity is Mathlib's `RegularSpace` class and the product carries the
standard product topology.
-/

theorem apm_tunk02
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [RegularSpace X] [RegularSpace Y] :
    Nonempty (RegularSpace (X × Y)) := by
  sorry

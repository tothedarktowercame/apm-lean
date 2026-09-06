import Mathlib

/-!
# APM t94J10 — products of regular spaces

The theorem states the requested product result directly, using Mathlib's
`RegularSpace` predicate on each factor and on the product topology.
-/

theorem apm_t94j10
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [RegularSpace X] [RegularSpace Y] :
    RegularSpace (X × Y) := by
  sorry

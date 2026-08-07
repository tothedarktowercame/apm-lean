import Mathlib

/-!
# APM t95A02 — compactness of the domain of a perfect map

## Statement repairs

The TeX is missing the closing `$` after `y ∈ Y`; this is only a typesetting
repair and does not change the mathematics.

## Encoding questions

None. Perfectness is expanded into Mathlib's native continuity, closed-map,
surjectivity, and compact-fibre predicates.
-/

open Set

def apm_t95A02_IsPerfectMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop :=
  Continuous f ∧ IsClosedMap f ∧ Function.Surjective f ∧
    ∀ y : Y, IsCompact {x : X | f x = y}

theorem apm_t95a02
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] (f : X → Y)
    (hf : apm_t95A02_IsPerfectMap f) :
    IsCompact (Set.univ : Set X) := by
  sorry

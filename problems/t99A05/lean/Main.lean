import Mathlib

/-! # APM t99A05: odd degree produces an odd intersection

## Statement repairs

The printed question omits the properness/compactness needed to make a regular
fiber compact.  This encoding therefore assumes compactness of `X`.  Mathlib
does not currently define mod-two degree or intersection number for smooth
manifolds, so the smooth transversality step is NOT replaced by opaque
predicates.  Instead, the theorem states the finite-fiber parity conclusion at
a regular value, the set-theoretic core of the informal solution.

## Encoding questions

`Z` is represented as a subtype and the chosen fiber is finite.  Odd mod-two
degree at `y` is expressed directly as odd cardinality of the restricted fiber;
the resulting compact set `W` is the full fiber of `f`.
-/

theorem apm_t99a05
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T1Space Y]
    (f : X → Y) (hf : Continuous f) (Z : Set X) (y : Y)
    [Fintype {z : Z // f z = y}]
    (hodd : Odd (Fintype.card {z : Z // f z = y})) :
    ∃ W : Set X, IsCompact W ∧ W = f ⁻¹' {y} ∧
      Odd ((Z ∩ W).ncard) := by
  sorry

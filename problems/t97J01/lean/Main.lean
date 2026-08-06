import Mathlib

/-!
# APM t97J01

## Statement repairs

The printed claim omits the necessary assumption that the covering space `X`
is Hausdorff. Without it, the identity map of any connected non-Hausdorff
space is a one-sheeted covering and is an immediate counterexample. The
minimal `T2Space X` hypothesis is therefore added.

## Encoding questions

A finite cover is encoded as an actual Mathlib `IsCoveringMap` whose fibers
are finite sets. Connectedness is retained for both spaces exactly as printed.
-/

open Set

theorem apm_t97j01
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [ConnectedSpace Y] [T2Space X]
    (p : X → Y) (hp : IsCoveringMap p)
    (hfinite : ∀ y : Y, (p ⁻¹' ({y} : Set Y)).Finite) :
    T2Space Y := by
  sorry

import Mathlib

/-! # APM tunk03: closed equivalence relations and Hausdorff quotients

## Statement repairs

None.

## Encoding questions

The equivalence relation is a `Setoid`; `Quotient s` has its quotient topology
and `Quotient.mk'` is the projection.  Closedness is imposed on the literal
relation subset of `X × X`, and Hausdorffness is Mathlib's `T2Space` property.
-/

theorem apm_tunk03
    {X : Type*} [TopologicalSpace X] (s : Setoid X)
    (hopen : IsOpenMap (Quotient.mk' : X → Quotient s)) :
    IsClosed {p : X × X | s.r p.1 p.2} ↔ T2Space (Quotient s) := by
  sorry

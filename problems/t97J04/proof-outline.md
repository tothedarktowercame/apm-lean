# Proof Outline: t97J04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J04.md`

## Compiled progress

- `apm_t97J04_inl_base_eq_inr_base` proves that the torus and circle
  basepoints coincide in the EqvGen quotient.

## Remaining bridges

1. Apply Seifert--van Kampen to the quotient wedge and identify the result
   with `PresentedGroup {apm_t97J04_relator}`.
2. Establish a singular Mayer--Vietoris sequence (or cellular-to-singular
   comparison) for the wedge.
3. Compute the torus and circle terms, yielding ranks `1, 3, 1` and vanishing
   above degree two.

The closest sibling, `t02A03`, encodes the same wedge and confirms these APIs
are not currently packaged in Mathlib.

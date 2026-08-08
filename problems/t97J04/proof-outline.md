# Proof Outline: t97J04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J04.md`

## Compiled progress

- `apm_t97J04_inl_base_eq_inr_base` proves that the torus and circle
  basepoints coincide in the EqvGen quotient.
- `apm_t97J04_wedgeQuotient` is the continuous surjective quotient map, and
  `apm_t97J04_torusInclusion` / `apm_t97J04_circleInclusion` are continuous.
- `apm_t97J04_wedgeDesc` descends every compatible pair of continuous maps;
  its computation and uniqueness lemmas establish the full continuous
  pushout eliminator. This follows the reusable pattern in sibling `t02A03`.

## Remaining bridges

1. Apply Seifert--van Kampen to the quotient wedge and identify the result
   with `PresentedGroup {apm_t97J04_relator}`.
2. Establish a singular Mayer--Vietoris sequence (or cellular-to-singular
   comparison) for the wedge.
3. Compute the torus and circle terms, yielding ranks `1, 3, 1` and vanishing
   above degree two.

Mathlib's categorical `IsVanKampenColimit` concerns stability of categorical
colimits and is not the topological fundamental-group theorem. Its available
Mayer--Vietoris sequences concern sheaf cohomology rather than singular
homology. Thus the point-set pushout interface is complete, but neither API
computes the frozen invariants.

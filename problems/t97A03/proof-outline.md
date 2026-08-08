# Proof Outline: t97A03

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97A03.md`

## Compiled progress

- `apm_t97A03_surjective_of_fiber_card_two` proves the cover map is onto from
  the frozen assertion that every fiber has cardinality two.
- The north and south attachment equalities in the concrete base quotient are
  now compiled directly from the generating relation.

## Remaining bridges

1. Identify the base quotient with `S² ∨ S¹ ∨ S¹` and compute its fundamental
   group as `F₂`.
2. Classify connected double covers by index-two subgroups and construct
   homeomorphisms with the one-circle or two-circle quotient models.
3. Relate their explicit lifted CW structures to singular homology, obtaining
   `H₀ = ℤ`, `H₁ = ℤ³`, `H₂ = ℤ²`, and vanishing above degree two.
4. Combine covering-space `π₁` injection with the finite-index
   Nielsen--Schreier equality to identify the group as `F₃`.

Mathlib currently lacks the covering classification, cellular-homology
comparison, and quantitative free-rank equality required by this chain.

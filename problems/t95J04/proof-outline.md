# Proof Outline: t95J04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t95J04.md`

## Compiled progress

- `t95J04_exists_missed_point` extracts an omitted target point from the
  dimension-gap consequence carried by every `T95J04SmoothMap`; formal Sard is
  therefore no longer part of the remaining proof.
- Explicit coordinate points prove nonemptiness of `S⁶`, `S² × S⁴`, and
  `S³ × S³`, closing the first field of each simple-connectivity predicate.

## Remaining bridges

1. Contract the complement of the omitted sphere point. Mathlib supplies the
   stereographic open partial homeomorphism, but not the assembled contraction
   or resulting null-homotopy.
2. Prove the fundamental groups of the relevant spheres, and hence their
   products, are subsingletons.
3. Compute enough integral homology of spheres and products to distinguish the
   three carriers: degree two separates `S² × S⁴`, while degree three separates
   `S³ × S³`.

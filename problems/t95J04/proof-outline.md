# Proof Outline: t95J04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t95J04.md`

## Compiled progress

- `t95J04_sphere_nonempty` constructs an explicit coordinate point on every
  encoded sphere. Its three specializations prove nonemptiness of `S⁶`,
  `S² × S⁴`, and `S³ × S³`, removing that input from later
  simple-connectivity constructions.

## Remaining bridges

1. Prove the Hausdorff-measure-zero image statement by a manifold-domain Sard
   theorem. Available Mathlib Sard lemmas concern normed vector spaces.
2. Contract the complement of an omitted sphere point. Mathlib supplies the
   stereographic open partial homeomorphism, but not the assembled contraction
   or resulting null-homotopy.
3. Prove the fundamental groups of the relevant spheres, and hence their
   products, are subsingletons.
4. Compute enough integral homology of spheres and products to distinguish the
   three carriers: degree two separates `S² × S⁴`, while degree three separates
   `S³ × S³`.

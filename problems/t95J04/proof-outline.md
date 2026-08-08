# Proof Outline: t95J04

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t95J04.md`

## Compiled progress

- `t95J04_sphere_nonempty` constructs an explicit coordinate point on every
  encoded sphere. Its three specializations prove nonemptiness of `S⁶`,
  `S² × S⁴`, and `S³ × S³`, removing that input from later
  simple-connectivity constructions.
- `t95J04_contractibleSpace_sphere_complement` transports the contraction of
  a vector space through Mathlib's stereographic homeomorphism, proving that
  every punctured target sphere is contractible. This generalizes the
  construction in solved helper layer `t94J05`.
- `t95J04_nullHomotopic_of_not_surjective` factors an arbitrary continuous
  map through a missed point's complement and descends its contraction. Hence
  the null-homotopy clause in part (a) is now reduced entirely to the already
  requested non-surjectivity conclusion.

## Remaining bridges

1. Prove the Hausdorff-measure-zero image statement by a manifold-domain Sard
   theorem. Available Mathlib Sard lemmas concern normed vector spaces.
2. Prove positive `μH[n]` measure of the encoded sphere, allowing image
   nullity to imply non-surjectivity.
3. Prove the fundamental groups of the relevant spheres, and hence their
   products, are subsingletons.
4. Compute enough integral homology of spheres and products to distinguish the
   three carriers: degree two separates `S² × S⁴`, while degree three separates
   `S³ × S³`.

# Proof Outline: t02A03

The frozen Lean theorem is present in `lean/Main.lean`. The canonical map from
the disjoint union `T² ⊕ S¹` to the generated-relation wedge quotient is now
explicit, continuous, and surjective.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A03.md`

## Remaining boundary

- compute `FundamentalGroup Circle 1` and specialize product preservation to
  the torus;
- identify the generated-relation quotient with a topological pushout suitable
  for van Kampen;
- establish singular Mayer--Vietoris or a cellular-to-singular comparison for
  the wedge;
- derive the displayed fundamental-group and homology isomorphisms.

Existing Mayer--Vietoris APIs concern sheaf cohomology, not this singular
homology functor.

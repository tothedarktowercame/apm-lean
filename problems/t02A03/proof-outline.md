# Proof Outline: t02A03

The frozen Lean theorem is present in `lean/Main.lean`. The canonical map from
the disjoint union `T² ⊕ S¹` to the generated-relation wedge quotient is now
explicit, continuous, and surjective.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A03.md`

## Compiled progress

- The quotient projection is continuous and surjective.
- `apm_t02a03_torusInclusion` and `apm_t02a03_circleInclusion` give continuous
  maps of the two summands into the wedge.
- `apm_t02a03_inclusions_basepoint_eq` proves their attaching-point images
  agree, and both images are identified with `apm_t02a03_ybase`.

## Remaining boundary

- compute `FundamentalGroup Circle 1` and specialize product preservation to
  the torus;
- identify the generated-relation quotient with a topological pushout suitable
  for van Kampen;
- establish singular Mayer--Vietoris or a cellular-to-singular comparison for
  the wedge;
- derive the displayed fundamental-group and homology isomorphisms.
- connect the compiled based cocone to future van Kampen and singular
  Mayer--Vietoris interfaces.

Existing Mayer--Vietoris APIs concern sheaf cohomology, not this singular
homology functor.

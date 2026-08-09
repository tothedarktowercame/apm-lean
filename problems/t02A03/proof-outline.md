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
- `apm_t02a03_wedgeDesc` is the continuous pushout eliminator for compatible
  maps out of the two summands; its restriction equations and uniqueness are
  compiled.

## Remaining boundary

- compute `FundamentalGroup Circle 1` and specialize product preservation to
  the torus;
- establish singular Mayer--Vietoris or a cellular-to-singular comparison for
  the wedge;
- derive the displayed fundamental-group and homology isomorphisms.
- apply future van Kampen and singular Mayer--Vietoris interfaces to the now
  compiled continuous pushout universal property.

Existing Mayer--Vietoris APIs concern sheaf cohomology, not this singular
homology functor.

## Hop 4 bridge statements

- `apm_t02A03_bridge_1` states the missing based torus fundamental-group
  computation.
- `apm_t02A03_bridge_2` states the exact fundamental-group and degreewise
  singular-homology computation for the compiled wedge pushout.

Together their conclusions are precisely the conjuncts of the frozen main
theorem.  Their proofs are intentionally left open for subsequent work.

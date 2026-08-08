# Proof Outline: t01J03

The frozen Lean theorem is present in `lean/Main.lean`. Continuity of the
boundary-torus inclusion into the solid torus is now a compiled reusable
lemma rather than duplicated inline topology reasoning.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J03.md`

## Compiled progress

- `apm_t01J03_continuous_boundaryInclusion` proves continuity of the boundary
  embedding.
- `apm_t01J03_gluedInl` and `apm_t01J03_gluedInr` expose the two canonical
  maps into the quotient, with compiled continuity lemmas.
- `apm_t01J03_gluedInl_boundary_eq_gluedInr` proves the cocone compatibility
  equation imposed by the gluing homeomorphism.
- `apm_t01J03_gluedDesc` descends every compatible pair of continuous maps
  from the two pieces to the quotient. Its restriction equations and
  `apm_t01J03_gluedDesc_unique` establish the full function-level continuous
  pushout universal property.

## Remaining boundary

- compute the based fundamental group of `Circle` and specialize product
  preservation to the torus and solid torus;
- establish a van Kampen theorem for the generated-relation quotient;
- establish singular Mayer--Vietoris or a cellular-to-singular comparison for
  the same gluing;
- transport the twice-spiral relation through those computations.
- connect the now-compiled continuous pushout universal property to whichever
  van Kampen or singular Mayer--Vietoris interface becomes available.

Mathlib's existing Mayer--Vietoris sequence concerns sheaf cohomology and does
not apply to the singular-homology functor in this statement.

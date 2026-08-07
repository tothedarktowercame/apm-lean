# Proof Outline: t01J03

The frozen Lean theorem is present in `lean/Main.lean`. Continuity of the
boundary-torus inclusion into the solid torus is now a compiled reusable
lemma rather than duplicated inline topology reasoning.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J03.md`

## Remaining boundary

- compute the based fundamental group of `Circle` and specialize product
  preservation to the torus and solid torus;
- establish a van Kampen theorem for the generated-relation quotient;
- establish singular Mayer--Vietoris or a cellular-to-singular comparison for
  the same gluing;
- transport the twice-spiral relation through those computations.

Mathlib's existing Mayer--Vietoris sequence concerns sheaf cohomology and does
not apply to the singular-homology functor in this statement.

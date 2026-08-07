# Proof Outline: t94J05

The frozen theorem is encoded in `lean/Main.lean`. Two elementary topology
bridges are now compiled: a nonsurjective map factors through a missed point's
complement, and a null-homotopy of that factor descends to the sphere-valued
map.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94J05.md`

## Remaining boundary

- connect the opaque `apm_t94J05_IsSmooth` predicate to a concrete smoothness
  notion and prove the Sard/non-surjectivity consequence;
- use Mathlib's stereographic partial homeomorphism to contract a punctured
  three-sphere by scaling in its vector-space target;
- transport the resulting constant endpoint to the fixed north pole, using
  path connectedness of the sphere.

The factorization and homotopy-composition bookkeeping no longer blocks these
steps.

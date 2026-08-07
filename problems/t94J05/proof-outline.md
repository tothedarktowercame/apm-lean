# Proof Outline: t94J05

The frozen theorem is encoded in `lean/Main.lean`. Two elementary topology
bridges are now compiled: a nonsurjective map factors through a missed point's
complement, and a null-homotopy of that factor descends to the sphere-valued
map.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94J05.md`

## Compiled progress

- Nonsurjective maps factor continuously through a missed-point complement.
- A complement-valued null-homotopy descends through subtype inclusion.
- `apm_t94J05_nullhomotopic_to_northPole` moves an arbitrary constant endpoint
  to the fixed north pole using path connectedness of `S³`.

## Remaining boundary

- connect the opaque `apm_t94J05_IsSmooth` predicate to a concrete smoothness
  notion and prove the Sard/non-surjectivity consequence;
- use Mathlib's stereographic partial homeomorphism to contract a punctured
  three-sphere by scaling in its vector-space target;
- construct the stereographic scaling homotopy with the available partial
  homeomorphism source/target membership proofs.

The factorization and homotopy-composition bookkeeping no longer blocks these
steps.

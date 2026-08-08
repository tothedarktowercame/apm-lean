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
- `apm_t94J05_contractibleSpace_complement` identifies the complement of any
  sphere point with its orthogonal complement via stereographic projection and
  transports the vector space's contractibility instance.
- `apm_t94J05_nullhomotopic_of_not_surjective` assembles factorization,
  contractibility, descent, and endpoint normalization to prove the full frozen
  conclusion for every nonsurjective map.

## Remaining boundary

- connect the opaque `apm_t94J05_IsSmooth` predicate to a concrete smoothness
  notion and prove the Sard/non-surjectivity consequence.

All topology after nonsurjectivity is now compiled; the opaque predicate has no
available eliminator, and the consulted Mathlib snapshot has no applicable
manifold Sard theorem.

# Proof Outline: t00J03

The canonical proof is complete in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00J03.md`

## Formal proof

- Surjectivity follows by choosing `Projectivization.rep` and applying
  `Projectivization.mk_rep`.
- Direct algebra proves the angle form is invariant under every generating
  representative change: simultaneous nonzero scaling cancels, and adding a
  radial tangent vector contributes zero to the alternating numerator.
- `Relation.EqvGen.rec` extends generator invariance to the equivalence closure,
  allowing the angle form to descend with `Quotient.lift`.
- On the unit half-circle and its velocity the descended form is identically
  one, by `sin² θ + cos² θ = 1`.
- Both oriented interval integrals therefore evaluate directly to `π` and
  `-π`.

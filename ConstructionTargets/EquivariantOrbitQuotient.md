# Equivariant homeomorphisms of literal orbit quotients

For groups `G` and `H` acting on topological spaces `E` and `F`, the
construction takes an arbitrary group isomorphism `a : G ≃* H`, a
homeomorphism `h : E ≃ₜ F`, and equivariance
`h (g • x) = a g • h x`. No topology on the groups or continuity of
their actions is required for this quotient comparison.

`inverse_equivariant` proves equivariance of the inverse using `a.symm`.
`orbit_forward` then supplies well-defined descent in both directions.
`quotientHomeomorph` constructs a homeomorphism from
`Quotient (MulAction.orbitRel G E)` to
`Quotient (MulAction.orbitRel H F)`, with their quotient topologies.
The forward map sends `[x]` to `[h x]`; the inverse sends `[y]` to
`[h.symm y]`. Quotient induction proves both inverse identities, and
the quotient topology supplies continuity of both descended maps.

For each source orbit `q`, `fiberHomeomorph` compares the literal fiber
of the source quotient map over `q` with the target quotient-map fiber
over `quotientHomeomorph a h he q`. Its evaluation is exactly `x ↦ h x`.
`fiber_card` transports `Nat.card` between these fibers; in particular
it gives equality of their finite cardinalities when the fibers are finite.

The Lean file is an exact promotion of `/tmp/EquivariantOrbitQuotient.lean`,
SHA256 `13ba5e296dade5ed73cca6b7cdeaea31b567a11f7e778a88fc1e5beb96a01260`.
Validation comprises fixture and canonical compilation, the focused Lake
build, eight printed axiom audits allowing only `propext`, `Classical.choice`
and `Quot.sound`, and forbidden-token and exact-scope checks.

This packet proves quotient descent and fiber comparison. The parent must
still transport continuous actions, fiber-orbit equivalence and
disjoint-translate neighborhoods to construct target quotient-covering
data, and compile its concrete circle example. Covering neighborhoods,
graph gluing, classification and frozen consumer closure are not established
here.

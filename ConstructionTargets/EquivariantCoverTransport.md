# Equivariant transport of orbit-quotient coverings

For groups `G`, `H` acting on topological spaces `E`, `F`, take a group
isomorphism `a : G ≃* H`, a homeomorphism `h : E ≃ₜ F`, and equivariance
`h (g • x) = a g • h x`. The source premise is actual
`IsQuotientCoveringMap` data for the literal `G`-orbit quotient projection.

`transport` constructs the target `IsQuotientCoveringMap` data. Each target
group element acts continuously because its action is the conjugate through
`h` of the source action of `a.symm g`. Equality in the literal quotient is
exactly the orbit relation. A source disjoint-translate neighborhood at
`h.symm x` becomes its image under `h`; an intersection of target translates
pulls back to an intersection for `a.symm g`, forcing `g = 1`.
`covering` derives `IsCoveringMap` for the target projection from these data.

The imported `EquivariantOrbitQuotient` constructs the forward homeomorphism
from the source literal orbit quotient to the target literal orbit quotient,
sending `[x]` to `[h x]`. Its inverse is induced by `h.symm`. The corresponding
fiber homeomorphism sends `x` to `h x` and preserves `Nat.card`. Neither the
quotient homeomorphism nor a target covering is supplied as a premise.

The concrete example constructs the circle point with complex value `-1`
and the finite subgroup `{1, minusOne}`. Its discreteness gives the source
orbit-quotient covering. Multiplication by any `c : Circle` is an equivariant
homeomorphism for this subgroup action. `translated_circle_cover` applies
the transport construction, and `translated_circle_quotient_mk` proves the
representative equation `[x] ↦ [c*x]` for its constructed quotient map.

The Lean source exactly promotes `/tmp/EquivariantCoverTransport.lean`,
SHA256 `adb54dee9d408d11af96f22a2c703886566fa40293cb709a035b223ee36ba266`.
It imports the quotient comparison at commit
`ae29dbf4336057f43e95c7aed1a9e03f9b75858f`. Validation includes fixture and
canonical compilation, the focused build, and eleven printed standard-only
axiom audits, five of which audit the imported quotient and fiber results.

Frozen consumer assembly, graph gluing, deck classification and surface
Euler multiplicativity remain separate obligations. No frozen consumer
closure is claimed.

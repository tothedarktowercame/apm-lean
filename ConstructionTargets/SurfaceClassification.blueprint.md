# Surface consumer foundations blueprint

Status: replacement blueprint awaiting independent review.

Source audit: `~/notes/closer/routes/surfaces.md`, reviewed by claude-14 on
2026-10-12. This blueprint supersedes the triangulation-first surface
classification program. No frozen consumer asks for a triangulation object;
the reusable outputs below are the homeomorphisms, cover classifications, and
cutting results that their remaining bridges actually consume.

The existing declarations in `SurfaceClassification.lean` remain banked. They
may supply local chart evidence, but they are not prerequisites for every node
below and the abandoned B4--B14 chain must not be resumed.

## Fixed representation boundaries

`ConstructionTargets.Surfaces.Surface` is an `EqvGen` polygon quotient.
Mathlib's quotient-covering theorem applies to `MulAction.orbitRel`, not to an
arbitrary `EqvGen`. Any use of that theorem therefore depends on an explicit
homeomorphism to an orbit quotient. Likewise, the glued surface in `t03J02`
must be identified with a `TopCat` pushout before van Kampen or
Mayer--Vietoris is applied.

Homology hypotheses on an arbitrary compact surface do not by themselves
provide a fundamental-group presentation. Such consumers first require a
homeomorphism to a standard surface model.

## R1. Polygon quotient model conversion

Consumers: `t00A02`, `t91J05`, `t97J02`.

For only the polygon quotients used by these consumers, construct an orbit
quotient with the required continuous properly discontinuous action and prove
an explicit homeomorphism from the existing `EqvGen` quotient. Record the
direction of every comparison. Do not claim definitional equality.

## R2. Connected finite-cover classification by monodromy

Consumers: `t00A02`, `t91J05`, `t94J04`, `t97J02`.
Depends on: R1 for concrete polygon bases.

Package a connected finite cover by the transitive action of the base
fundamental groupoid on one finite fiber. Prove that an equivariant bijection
of fiber actions induces a homeomorphism of covering spaces. Use Mathlib's
path lifting, homotopy lifting, `monodromy`, and `monodromy_bijective` APIs.

## R3. Requested concrete finite covers

Consumers: `t00A02`, `t91J05`, `t97J02`.
Depends on: R1, R2.

Construct only the degrees in the frozen statements: odd covers of the
genus-three orientable model, the three covers of the nonorientable genus-four
model, and the regular/nonregular four-fold wedge covers. Keep action
transitivity and fiber-cardinality proofs separate from quotient topology.

## R4. Compact surface recognition

Consumers: `t00A02`, `t00A03`, `t01J01`, `t92J05`, `t94J04`.

Prove a reusable recognition theorem whose hypotheses match the consumers:
a compact connected Hausdorff two-manifold with the stated orientability and
genus-homology data is homeomorphic to the corresponding standard polygon
surface. Every manifold, connectedness, compactness, and homology hypothesis
must be used. This is the large classification result; it is not routed
through a separately exposed finite-triangulation theorem.

## R5. Standard-model presentations and finite-index subgroups

Consumers: `t92J05`, `t94J04`, `t96A01`.
Depends on: R2, and R4 except for `t96A01`, whose statement already supplies
the homeomorphism to `Surface true 4`.

Prove only the requested standard-surface fundamental-group presentations and
finite-index subgroup identifications, then transport them through the given
or R4 homeomorphisms. Reuse the compiled Euler arithmetic in the consumers.

## R6. Cutting and collar consequences

Consumers: `t00A03`, `t01J01`.
Depends on: R4.

On the standard models, prove separation of a null-homologous embedded circle,
the annulus/collar theorem for disjoint essential separating circles, and the
pants-decomposition incidence count needed by the frozen bridges. Transport
the results through R4. Existing nested-triangle and Schoenflies declarations
may supply local chart and closed-range facts only.

## R7. Glued quotient as a pushout

Consumer: `t03J02`.

Prove that the concrete glued quotient satisfies the `TopCat` pushout
universal property. Then add the required van Kampen and singular
Mayer--Vietoris specializations for the concrete torus factors. This node is
independent of R4 and must not be folded into closed-surface classification.

## Replacement action

The supervisor should retire `compactSmoothSurfaceFiniteTriangulation` as the
program's final declaration and elect separate rows for R1--R7 in dependency
order, sharing R2 and R4 across their named consumers. Existing proved
`FiniteTwoComplex`, disk-cover, and polygonal-path lemmas remain banked but do
not justify continuing the abandoned triangulation chain.

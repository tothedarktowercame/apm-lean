# t00A01 blueprint (revision 2)

## Triage verdict: unfaithful

`Main.lean` is weaker than the informal problem at its geometric input. The
problem permits `φᵢ(D³)` to be a 3-simplex of a triangulation; `Main.lean`
retains only `Topology.IsEmbedding φᵢ`. Arbitrary embedded closed 3-balls can
be wild, and their complements need not have the fundamental group or collar
used by the informal proof. Formalizing a wild ball is far outside Mathlib, so
there is no useful short `Refute.lean`.

`RevisedMain.lean` adds for each `φᵢ` only
`apm_t00A01_HasBallCollar φᵢ`: an extension to an embedding of the closed
radius-two ball which agrees on the unit ball and maps the open radius-two ball
to an open subset. It retains every original hypothesis and the entire original
conclusion. This is warranted by the simplex assumption: a simplex in a
triangulated 3-manifold has a PL 3-ball neighbourhood (after the standard
subdivision/closed-star choice), which supplies such a collar.

The earlier repair was circular because it assumed the four consequences below.
Revision 2 makes all four conclusions of lemmas.

## Open lemmas

### `apm_t00A01_punctured_pathConnected` — LIBRARY

The complement of the open unit ball inside a collared ball embedding is path
connected. Obtain connectedness from `H₀(M;ℤ) ≅ ℤ`, use local path connectedness
of a manifold, and use radial detours in the collar to push paths off the deleted
interior. Estimate: 100–200 lines. Dependencies: none.

Truth checks: for standard `S³` the complement is `D³`; radius-one and
radius-two boundary points are retained. The collar excludes wild balls.

### `apm_t00A01_punctured_fundamentalGroup` — LIBRARY

The punctured manifold has fundamental group isomorphic to that of `M`. Apply
van Kampen to the union of a slightly enlarged punctured part and the open
collar ball. The ball is contractible and the overlap is an open shell
homotopy equivalent to `S²`, hence simply connected by
`ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected`.
Then change basepoints using the fundamental groupoid API. Estimate: 200–350
lines. Dependencies: the same geometric path-detour construction as the first
lemma; the conclusion is not passed as a hypothesis so seats remain independent.

Truth checks: for `S³` both groups are trivial; for a Poincaré homology sphere,
removing a tame ball preserves its binary-icosahedral fundamental group.

### `apm_t00A01_punctured_isHomologyBall` — LIBRARY

Deleting the collared open ball from an integral homology 3-sphere leaves an
integral homology ball. Use the pair long exact sequence, excision into the
radius-two chart, and the local orientation/fundamental-class comparison. The
key map `H₃(M) → H₃(M,M\\int D³)` sends the global fundamental class to a local
generator. Closest sorry-free modules:
`ConstructionTargets.HigherModelLocalHomology`,
`ConstructionTargets.HigherChartLocalGenerator`, and
`ConstructionTargets.ManifoldFundamentalClass`; missing is their relative-pair
assembly for this collar. Estimate: 300+ lines. Dependencies: none.

Truth checks: the exact sequence yields `H₀ = ℤ` and zero in positive degrees;
degrees 2 and 3 are precisely where the local-generator isomorphism is needed.

### `apm_t00A01_collared_standardCover` — LIBRARY

Construct two open collar-thickenings in the quotient, prove they cover,
deformation retract them to the punctured pieces, and radially retract their
intersection to the glued `S²`. The result also packages continuity of both
boundary maps. The topology ledger says the missing boundary is the actual-cover
inclusion comparisons and arbitrary-cover span translation. Closest sorry-free
infrastructure: `ConstructionTargets.TwoOpenFreeProductMapping` and the quotient
cocone/universal-property lemmas already in this file. Estimate: 300+ lines.
Dependencies: none.

Truth checks: radial coordinates use `1 < r < 2`, so the overlap is nonempty
and equivalent to `S²`; at radius one the copies agree by
`apm_t00A01_mk_inl_eq_mk_inr`. Endpoint and empty-overlap degeneracies are
excluded by the radius-two extension.

## Proved bridges and dependency layers

`apm_t00A01_bridge_fundamentalGroup_coprod` and
`apm_t00A01_bridge_connectedSum_isHomology3Sphere` are already sorry-free and
implement the van Kampen and degree-by-degree Mayer–Vietoris consumers. The
main theorem has no `sorry`; it obtains the four collar consequences and passes
them to these bridges.

- Layer 0 (parallel): the four LIBRARY lemmas above.
- Layer 1: `apm_t00a01` assembly, already proved.

## Axiom audit

Both Lean files compile. Final output:

```text
'apm_t00a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` enters only through the four named top-level LIBRARY lemmas.

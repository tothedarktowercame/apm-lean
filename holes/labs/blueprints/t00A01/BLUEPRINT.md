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

#### Split of `apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid`

`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_algebra` is an
independent, sorry-free categorical leaf (about 55 proof lines).  Its inputs
are an arbitrary standard-cover presentation and the single assertion that
`productionConnecting U V hU hV hUV 2` is an isomorphism.  In degree three it
uses
`MayerVietorisExactnessIsZero.isZero_middle_of_two_exact_of_isZero_left_of_mono_right`,
`productionMayerVietoris_exact_pieces`, and
`productionMayerVietoris_exact_union`; in degree two it cancels the epi
connecting map in `productionConnecting_comp_intersection` and uses
`productionMayerVietoris_exact_intersection`.  The homotopy transports use
`singularHomologyIsoOfHomotopyEquiv` and
`moduleHomologyIsoOfHomotopyEquiv`.  Truth check: for `S³` this is the usual
`0 → 0 → ℤ → ℤ → 0`; for the Poincaré sphere the same calculation is
unchanged because only integral homology enters.  The overlap cannot be empty:
its supplied homotopy equivalence to `S²` makes its `H₂` nonzero, while the
isomorphism hypothesis also rules out the zero connecting map.

`apm_t00A01_punctured_isHomologyBall_aux_positive_aux_mid_connecting` is the
remaining **LIBRARY** leaf (estimated 350–700 lines with the missing
foundation).  It states exactly what the algebra consumes, for explicit
cover witnesses: the production Mayer--Vietoris map
`H₃(M) → H₂(U ∩ V)` is an isomorphism.  The intended proof factors it, up to
the collar/excision sign, as
`H₃(M) → H₃(M,M\\{φ 0}) ≅ H₃(M,P) ≅ H₃(D,D\\int D) ≅ H₂(S²)`.
Use `ChartPairRelativeHomologyTransport`,
`HigherChartLocalGenerator`, `CoefficientManifoldLocalComparison`, and
`LocalHomologyNeighborhoodExcision.neighborhoodInclusion_chain_eq` for the
comparison squares, then the relative connecting naturality API to identify
the final map with `productionConnecting`.  The global input is Hatcher
Lemma 3.27/Theorem 3.26: induct over compact subsets covered by coordinate
balls to show that a normalized top-dimensional global class restricts to a
local generator at every point; compactness gives a finite subcover and
connectedness propagates the sign.  Since `H₃(M;ℤ) ≅ ℤ`, this restriction is
an isomorphism.  Truth checks: on `S³` it is degree `±1` according to collar
orientation; on a Poincaré homology sphere it is likewise `±1`, not the order
of the fundamental group.  Reversing the collar changes only the sign and
therefore not `IsIso`; boundarylessness is essential.

Important infrastructure gap: despite its general-sounding name, the current
proved theorem
`LocalHomologyNeighborhoodExcision.neighborhoodInclusion_H1_isIso` is fixed
to relative degree `1`.  There is presently no all-degree neighborhood
excision theorem in that module, nor a general closed-manifold fundamental
class localization theorem.  Consequently splitting the LIBRARY leaf into
separate, compilable pair-comparison leaves would require first adding those
foundations; pretending they exist would merely move the entire argument into
an overloaded hypothesis.  The `_aux_mid` assembly itself is sorry-free and
depends only on the two leaves above.

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

### Split of `_aux_right_aux_quotient` (claude-14, 2026-10-20, from job 119 / lemma-3)
lemma-3's 174-line proof was spliced in as the assembly. It said "compiles, sorryAx
hidden", but in fact two terms failed to elaborate (a `Set` used as a type without
`↥`, and the nonexistent `Continuous.prod_map`), and Lean turned both into sorry.
Repaired; the only sorry left is the new leaf
`apm_t00A01_collared_standardCover_aux_right_aux_quotient_aux_cont`: a map
`F : unitInterval × ↥(inl '' C ∪ range inr) → X` (C open) is continuous when its
restrictions to `unitInterval × C` and `unitInterval × B` are. Truth: both pieces map
by open embeddings (`IsOpenEmbedding.inl/inr`, `hC.isOpenEmbedding_subtypeVal`,
`IsOpenEmbedding.prodMap` with id) whose ranges cover; then `ContinuousOn.union_of_isOpen`.
C = ∅ is fine (the left piece is empty). The `hf` block of the assembly is the same proof
without the `unitInterval` factor and can be copied from there. Size: 30-60 lines.

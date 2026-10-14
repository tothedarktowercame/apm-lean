# t93J03 blueprint

## Triage

Verdict: **true and faithful**.  The registered theorem says both parts of the
problem at once: it supplies the printed presentation at every basepoint and,
relative to that presentation, gives a planar embedding for every subspace
whose induced fundamental group lies in `⟨a⟩`.

I tried the standard degenerate cases.  `X = ∅` is excluded because it cannot
have a `PathConnectedSpace` instance.  A singleton subspace has trivial
fundamental group, so its image lies in `⟨a⟩` and it plainly embeds in the
plane.  The whole Klein bottle cannot satisfy the subgroup hypothesis: under
the asserted equivalence its fundamental group maps onto the full presented
group, which contains the `b` direction, not only `⟨a⟩`.  Thus the statement
does not accidentally imply that the Klein bottle is planar.  The arbitrary
choice of presentation equivalence is existential and is fixed before `X`, as
the informal part (a) requires.

The semilocally simply connected hypothesis is not needed by the lifting
criterion once the required cover has been explicitly constructed.  It is
nevertheless retained verbatim because it is a hypothesis of `problem.md`.

## Shared definitions

`a`, `b`, `relations`, `PresentedKleinGroup`, `generatorA`,
`SemilocallySimplyConnected`, and `inclusion` are copied verbatim from
`problems/t93J03/lean/Main.lean`.  No predicate packages a desired conclusion.

## Lemmas

### Four-way split of `t93J03_kleinBottle_pi1_every_basepoint`

The original library lemma is now a sorry-free assembly of the following four
parallel leaves, mirroring the `t96J02` interface exactly.

#### `t93J03_kleinPlaneQuotient_pi1_origin`

Compute the fundamental group at the orbit of `(0,0)`.  Use
`DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`
with `KleinPlaneAffineAction.eq_one_of_smul_eq`.  The required action and its
proper discontinuity instances come through the imported Klein orbit-quotient
development.  Estimated proof: 30–60 lines.  Independent.

Truth check: the theorem identifies the fundamental group with the acting
group itself, not with an opposite group; the banked theorem's endpoint
monodromy includes the inversion correcting multiplication order.  Freeness
at the origin (indeed at every point) rules out stabilizer quotients.

#### `t93J03_kleinPlaneQuotient_pi1_every_basepoint`

Move the supplied origin calculation to an arbitrary quotient point.  Use
`PathConnectedSpace.somePath`, the basepoint-change isomorphism for
`FundamentalGroup`, and `MulEquiv.trans`.  Search Mathlib for
`FundamentalGroup.changeBasepoint` / `FundamentalGroupoid` vertex-group
transport if the exact API name has moved.  Estimated proof: 40–90 lines.
Independent because the origin result is an explicit hypothesis.

Truth check: the orbit quotient is path connected as a continuous image of
the path-connected plane, so every point admits a path from the origin.  No
claim is made for a disconnected space.

#### `t93J03_kleinPlaneQuotient_homeomorph` — LIBRARY

Identify the literal `MulAction.orbitRel.Quotient PresentedKleinGroup
(ℝ × ℝ)` with the frozen polygon `KleinBottle`.  Use
`KleinClosedSquareOrbitQuotientEquiv.closedSquareOrbitQuotientEquiv`,
`KleinOrbitQuotientHomeomorph.continuous_closedSquareOrbitQuotientEquiv`, and
the inverse-continuity results in
`KleinClosedSquareOrbitInverseContinuity`; then compare the closed-square edge
setoid with `StatementSurfaceModels.KleinBottle`.  Estimated proof: 90–150
lines if the final comparison API is present; otherwise this remains the one
genuine 180–300 line library foundation.  Independent.

Truth check: the affine generators act as horizontal translation and vertical
glide reflection, producing precisely the frozen Klein edge orientation, not
the torus orientation.  Empty-set and boundary-point issues do not arise:
the quotient is inhabited by the origin, and the closed-square development
explicitly handles corners and all four edges.

#### `t93J03_pi1_every_basepoint_of_homeomorph`

Generic transport across a supplied homeomorphism.  For `y`, take
`x := e.symm y`; use `Homeomorph.toContinuousMap`,
`FundamentalGroup.map`, and the inverse map to construct the group equivalence,
or use the existing fundamental-group equivalence induced by a homeomorphism.
Estimated proof: 30–70 lines.  Fully independent and not Klein-specific.

Truth check: choosing `e.symm y` makes the basepoints definitionally align
after simplification; no connectedness assumption is needed because this does
not move basepoints within either space.

#### `t93J03_kleinBottle_pi1_every_basepoint` (assembly)

The original registered library statement contains no `sorry`: obtain the
homeomorphism, feed the origin leaf to the all-basepoint quotient leaf, and
apply the generic transport leaf.  Estimated proof: 5 lines, complete.

### `t93J03_cyclicCover_zpowers_generatorA` — LIBRARY

**Statement.** Given the presentation equivalence at `k`, there is a covering
`p : C → KleinBottle`, a basepoint above `k`, and an embedding `C → ℝ²`
such that the range of the induced fundamental-group map is exactly the
preimage under `e` of `Subgroup.zpowers generatorA`.

**Why true.** Take the intermediate quotient of the affine plane by the
horizontal translation subgroup `⟨a⟩`.  It is an open cylinder, homeomorphic
to the punctured plane via polar coordinates, hence embeds in `ℝ²`.  Its
map to the full Klein quotient is a covering.  The endpoint/deck computation
identifies its induced subgroup with precisely `⟨a⟩`.  The conclusion is
written as a `Subgroup.comap` equality so the next lemma can use Mathlib's
lifting criterion without losing basepoint information.

This is the worklist's outstanding 250–450 line covering-subgroup library
component.  The closest sorry-free foundations are
`ConstructionTargets/DeckGroupQuotientFundamentalGroup.lean`,
`ConstructionTargets/KleinPlaneAffineAction.lean`, and
`ConstructionTargets/KleinPlaneActionFree.lean`; none currently constructs
this intermediate cylinder cover.

**Estimate.** 250–450 lines.

**Dependencies.** Takes the conclusion of
`t93J03_kleinBottle_pi1_every_basepoint` as an explicit parameter, so a seat
can develop it independently against that interface.

**Truth check.** Under the coordinate normal form, quotienting only by
horizontal integer translations leaves `S¹ × ℝ`; the loop around `S¹`
is the `a` generator.  At the zero/identity coordinate the subgroup is still
all integer powers of `a`, including exponent zero.

### `t93J03_coveringLift_of_subgroup_le`

**Statement.** For any supplied cover whose induced range is the preimage of
`⟨a⟩`, the hypothesis on `X` produces a continuous lift of the inclusion.

**Why true.** Rewrite membership in the supplied range using `hcover`, then
apply
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`
(`Mathlib/Topology/Homotopy/Lifting.lean`, theorem near line 439).  The only
bookkeeping is transport between the equality `p c = k` and
`p c = inclusion X x`, obtained from `hx`.

**Estimate.** 30–80 lines.

**Dependencies.** Takes the complete conclusion of the cyclic-cover lemma as
hypotheses; it does not invoke that lemma, so it can be proved in parallel.

**Truth check.** For the singleton test case the range is trivial and the
criterion returns the constant lift at the chosen point above `k`.  More
generally, applying `e` to each element of the induced range gives exactly the
stated subgroup inclusion.

### `t93J03_lift_isEmbedding_assembly` (already proved)

**Statement.** A lift of the subtype inclusion is an embedding, and composing
it with an embedding of the cover gives a planar embedding.

**Why true.** `Topology.IsEmbedding.of_comp` cancels the continuous covering
projection from `p ∘ l = Subtype.val`; then `Topology.IsEmbedding.comp`
composes with `jC`.  This proof is included without `sorry` in the blueprint.

**Estimate.** 8 lines (already complete).

**Dependencies.** Only the continuous lift returned by the preceding lemma;
the statement accepts that lift as a hypothesis.

**Truth check.** Injectivity is immediate: equal lifted points have equal
images under `p`, and subtype inclusion is injective.  The formal proof also
checks the induced-topology part through embedding cancellation.

## Dependency layers

- Layer 1 (parallel): the four new Klein fundamental-group leaves,
  `t93J03_coveringLift_of_subgroup_le`, and the already completed
  `t93J03_lift_isEmbedding_assembly`.
- Layer 2a: the sorry-free `t93J03_kleinBottle_pi1_every_basepoint` assembly.
- Layer 2: `t93J03_cyclicCover_zpowers_generatorA` (LIBRARY), against the
  explicit equivalence interface supplied by the assembly.  Much of its
  geometric construction can proceed in parallel with layer 1.
- Layer 3: the main theorem assembly, already complete and sorry-free.

The principal risk remains implementation size of the literal orbit-quotient
homeomorphism, not the mathematical statement.  All four leaves are statable
and provable independently because every cross-leaf conclusion is an explicit
hypothesis.

## Compile and axiom gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93J03/Blueprint.lean
```

Output of `#print axioms apm_t93j03`:

```text
'apm_t93j03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem itself and the original fundamental-group library theorem
contain no `sorry`; `sorryAx` enters only through the new leaves and the
pre-existing cyclic-cover lemma.

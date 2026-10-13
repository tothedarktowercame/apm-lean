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

### `t93J03_kleinBottle_pi1_every_basepoint` — LIBRARY

**Statement.** For every `k : KleinBottle`, the fundamental group at `k` is
isomorphic to the frozen presented Klein group.

**Why true.** Use the banked affine action of `PresentedKleinGroup` on
`ℝ × ℝ`, the missing homeomorphism from its literal
`MulAction.orbitRel.Quotient` to the frozen polygon `KleinBottle`, and
`DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`.
Freeness is already proved by
`KleinPlaneAffineAction.eq_one_of_smul_eq`; the coordinate model and normal
form are also banked.  Transport from the quotient basepoint to arbitrary `k`
uses path connectedness/basepoint change.

The topology worklist explicitly warns that
`ConstructionTargets/KleinOrbitQuotientHomeomorph.lean` does **not** yet give
the required literal orbit-quotient homeomorphism.  This is the outstanding
180–300 line library component; it should not be disguised as several small
lemmas.

**Estimate.** 180–300 lines for the quotient homeomorphism, then 60–120 lines
for the fundamental-group adapter.

**Dependencies.** None among the blueprint lemmas (but it depends on the
banked ConstructionTargets listed above).

**Truth check.** The identity element fixes the chosen plane basepoint, and
the banked freeness theorem shows no nonidentity element does.  The banked
coordinate equivalence sends the two generators to the expected translation
and glide-reflection coordinates, so the deck group is exactly the printed
presentation rather than an accidental quotient.

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

- Layer 1 (parallel): `t93J03_kleinBottle_pi1_every_basepoint` (LIBRARY),
  `t93J03_coveringLift_of_subgroup_le`, and the already completed
  `t93J03_lift_isEmbedding_assembly`.
- Layer 2: `t93J03_cyclicCover_zpowers_generatorA` (LIBRARY), against the
  explicit equivalence interface supplied by layer 1.  Much of its geometric
  construction can proceed in parallel with layer 1.
- Layer 3: the main theorem assembly, already complete and sorry-free.

There are four top-level blueprint lemmas, two of them marked LIBRARY and one
already proved.  I am convinced all four statements are true.  The principal
risk is implementation size of the literal orbit-quotient homeomorphism, not
the mathematical statement.

## Compile and axiom gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93J03/Blueprint.lean
```

Output of `#print axioms apm_t93j03`:

```text
'apm_t93j03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem itself contains no `sorry`; `sorryAx` enters only through the
three unfinished top-level lemmas.

# t93J03 closure blueprint

Source: `holes/labs/blueprints/t93J03/BLUEPRINT.md` (reviewed closure plan).
The frozen definitions and theorem are in `problems/t93J03/lean/Main.lean`; the
compiled reference assembly is `holes/labs/blueprints/t93J03/Blueprint.lean`.

## Triage

The registered theorem is true and faithful. It combines the printed
fundamental-group presentation at every basepoint with a planar embedding for
each path-connected subspace whose induced fundamental group lies in
`Subgroup.zpowers generatorA`. The presentation equivalence is chosen before
the subspace. Empty subspaces are excluded by `PathConnectedSpace`; singleton
subspaces satisfy the subgroup condition; the whole Klein bottle does not.

### Frozen redundant hypothesis — owner-approved

The semilocally simply connected hypothesis is mathematically redundant once
the cyclic cover is explicitly constructed. Mathlib's subgroup lifting
criterion used by C3 assumes path connectedness and local path connectedness,
but not semilocal simple connectedness. C4 derives the embedding only from the
lift equation and the two embeddings. Thus C1--C4 prove the final conclusion
without this hypothesis, exactly as the compiled reference's
`intro X _ _ _ x hx hX` records.

The previous repair paired a witness extracted from this hypothesis with the
independently proved lift. That was vacuous and is retracted: the final theorem
does not mention the witness, so C5 necessarily discarded it. No proof step in
this route has a result that genuinely depends on the hypothesis.

Owner decision (claude-14, 2026-10-13): the hypothesis-coverage gate does not
apply to hypotheses mandated by `problem.md`. Keep this frozen hypothesis
anonymous and unused, record it as `unused-mandated`, and use the stronger
lifting theorem. Formalisation must not manufacture a dependency.

## Frozen shared definitions

Copy `a`, `b`, `relations`, `PresentedKleinGroup`, `generatorA`,
`SemilocallySimplyConnected`, and `inclusion` verbatim from
`problems/t93J03/lean/Main.lean`. Do not package a desired conclusion into a
predicate and do not change the registered theorem or these definitions.

## Milestones

### C1. `t93J03_kleinBottle_pi1_every_basepoint` — LIBRARY

For every `k : KleinBottle`, construct an equivalence between
`FundamentalGroup k` and the frozen `PresentedKleinGroup`.

Use the banked affine action of `PresentedKleinGroup` on `ℝ × ℝ`, the literal
homeomorphism from `MulAction.orbitRel.Quotient` to the frozen polygon model,
and
`DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`.
Freeness is supplied by `KleinPlaneAffineAction.eq_one_of_smul_eq`; the
coordinate model and normal form are banked. Transport from the quotient
basepoint to arbitrary `k` by path-connected basepoint change.

The missing literal orbit-quotient homeomorphism is the substantive first
component (estimated 180–300 lines); the fundamental-group adapter is then
estimated at 60–120 lines. Do not replace the literal quotient by a merely
similar quotient. Check that the two generators map to translation and
glide-reflection coordinates, so the result is the printed presentation and
not a quotient of it.

Dependencies: banked deck-group quotient, affine action, action freeness, and
coordinate normal form. No dependency on another blueprint lemma.

### C2. `t93J03_cyclicCover_zpowers_generatorA` — LIBRARY

Given the C1 presentation equivalence at `k`, construct a covering
`p : C → KleinBottle`, a point over `k`, and an embedding `C → ℝ²`, with the
range of the induced fundamental-group map equal to the preimage under the
equivalence of `Subgroup.zpowers generatorA`.

Take the intermediate quotient of the affine plane by the horizontal
translation subgroup `⟨a⟩`. It is an open cylinder, homeomorphic to the
punctured plane by polar coordinates, and therefore embeds in `ℝ²`. Its map to
the full Klein quotient is a covering. The endpoint/deck computation must
identify its induced subgroup exactly with `⟨a⟩`; retain the conclusion as a
`Subgroup.comap` equality for the lifting criterion.

This is the outstanding 250–450 line covering-subgroup component. Reuse
`DeckGroupQuotientFundamentalGroup`, `KleinPlaneAffineAction`, and
`KleinPlaneActionFree`; none currently constructs this intermediate cover.
C2 takes C1's equivalence as an explicit parameter.

### C3. `t93J03_coveringLift_of_subgroup_le`

For a supplied cover whose induced range is the preimage of `⟨a⟩`, derive a
continuous lift of the subtype inclusion from the subgroup hypothesis.

Rewrite membership in the induced range using the supplied equality, then use
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` from
`Mathlib/Topology/Homotopy/Lifting.lean`. Transport the basepoint equality
between `p c = k` and `p c = inclusion X x` using the chosen point of `X`.
This lemma accepts the cover interface as hypotheses and does not invoke C2.
The generalized compiled form is
`ConstructionTargets.t93J03Closure.coveringLift_of_subgroup_le`, parameterized
by the presented group and subgroup so it can be reused without duplicating
the frozen definitions.

### C4. `t93J03_lift_isEmbedding_assembly` — already proved

Cancel the continuous covering projection from
`p ∘ l = Subtype.val` using `Topology.IsEmbedding.of_comp`, then compose with
the planar embedding of the cover using `Topology.IsEmbedding.comp`. Copy the
compiled proof from `holes/labs/blueprints/t93J03/Blueprint.lean`.
The generalized compiled form is
`ConstructionTargets.t93J03Closure.lift_isEmbedding_assembly`.

### C5. Main theorem assembly — already proved

Copy the sorry-free assembly from the reference blueprint after C1–C4 are
available. It chooses the presentation equivalence, constructs the cyclic
cover, applies C3, and finishes with C4. The anonymous semilocal-simple-
connectedness argument is the frozen redundant hypothesis described above.

## Dependency layers

- Layer 1: C1, C3, and C4. C1 and C3 are independent; C4 is already complete.
- Layer 2: C2 against the explicit C1 equivalence interface.
- Layer 3: C5, already complete modulo C1 and C2.

Bank C1 and C2 separately as the two LIBRARY obligations. The principal risk
is the literal orbit-quotient homeomorphism and intermediate-cylinder cover,
not the frozen theorem.

Final-hypothesis audit: `SemilocallySimplyConnected X` is `unused-mandated`
under the owner decision above; all non-mandated proof inputs are consumed.

## Gates

Compile the reference with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93J03/Blueprint.lean
```

The reference currently reports `sorryAx` only through unfinished top-level
library lemmas. Final closure must compile
`problems/t93J03/lean/Main.lean`, pass the statement registry, contain no
`sorry` or new axioms, and depend only on standard axioms.

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

### Frozen redundant-hypothesis resolution

The semilocally simply connected hypothesis is mathematically redundant once
the cyclic cover is explicitly constructed: Mathlib's subgroup lifting
criterion needs path connectedness and local path connectedness, but not
semilocal simple connectedness.  The registered statement is frozen, so the
formal adapter must neither delete the hypothesis nor pretend that it is
needed to construct C1 or C2.

To satisfy the final-hypothesis audit honestly, C3 takes a named
`hslsc : SemilocallySimplyConnected X` argument and extracts its actual
content at the selected basepoint `x`:

```lean
obtain ⟨U, hUopen, hxU, hUloops⟩ := hslsc x
```

C3 returns this witness together with the lift, then applies the stronger
global subgroup lifting criterion for the lift component.  Thus the frozen
hypothesis is used according to its definition, while the blueprint explicitly
records that the resulting lift theorem is stronger and would remain true
without it.  C5 must bind the argument as `hslsc`, never `_`, and pass it to
C3.  This is the explicit resolution of the redundant frozen hypothesis; no
registered type is changed.

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

For a supplied cover whose induced range is the preimage of `⟨a⟩`, a named
`hslsc : SemilocallySimplyConnected X`, and the subgroup hypothesis, derive a
continuous lift of the subtype inclusion.

Its conclusion is deliberately certificate-bearing:

```lean
∃ U : Set X, IsOpen U ∧ x ∈ U ∧
  (∀ γ : Path x x, (∀ t, γ t ∈ U) → Path.Homotopic γ (Path.refl x)) ∧
  ∃ l : C(X, C), p ∘ l = inclusion X
```

Rewrite membership in the induced range using the supplied equality, then use
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` from
`Mathlib/Topology/Homotopy/Lifting.lean`. Transport the basepoint equality
between `p c = k` and `p c = inclusion X x` using the chosen point of `X`.
Before applying the global criterion, extract `⟨U, hUopen, hxU, hUloops⟩`
from `hslsc x`; return those four fields together with the lift produced by
the subgroup criterion. This lemma accepts the
cover interface as hypotheses and does not invoke C2.

### C4. `t93J03_lift_isEmbedding_assembly` — already proved

Cancel the continuous covering projection from
`p ∘ l = Subtype.val` using `Topology.IsEmbedding.of_comp`, then compose with
the planar embedding of the cover using `Topology.IsEmbedding.comp`. Copy the
compiled proof from `holes/labs/blueprints/t93J03/Blueprint.lean`.

### C5. Main theorem assembly — already proved

Copy the sorry-free assembly from the reference blueprint after C1–C4 are
available. It chooses the presentation equivalence, constructs the cyclic
cover, binds the frozen hypothesis as `hslsc`, passes `hslsc` to C3,
destructures both its neighborhood certificate and lift, and finishes with
C4. The reference line `intro X _ _ _ x hx hX` must therefore be repaired to
`intro X _ _ hslsc x hx hX`.

## Dependency layers

- Layer 1: C1, C3, and C4. C1 and C3 are independent; C4 is already complete.
- Layer 2: C2 against the explicit C1 equivalence interface.
- Layer 3: C5, already complete modulo C1 and C2.

Bank C1 and C2 separately as the two LIBRARY obligations. The principal risk
is the literal orbit-quotient homeomorphism and intermediate-cylinder cover,
not the frozen theorem.

Final-hypothesis gate: C5 passes every named hypothesis onward; specifically,
`hslsc` is consumed by C3's basepoint neighborhood witness extraction.

## Gates

Compile the reference with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93J03/Blueprint.lean
```

The reference currently reports `sorryAx` only through unfinished top-level
library lemmas. Final closure must compile
`problems/t93J03/lean/Main.lean`, pass the statement registry, contain no
`sorry` or new axioms, and depend only on standard axioms.

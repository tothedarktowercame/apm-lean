# Blueprint for t99J01

## Triage verdict

**True and faithful; no statement repair.**  The Lean theorem says exactly the
three claims in `problem.md`: existence of a connected positive-degree cover,
classification of every connected finite cover, and the componentwise answer
when disconnected covers are allowed.

Degenerate checks:

- `n = 0` is excluded only from the existence clause, as the problem requires.
  In the classification clauses an inhabited total space forces a nonempty
  fiber over `p e`, hence a purported zero-sheeted cover cannot occur.
- An empty total space causes no contradiction in the third clause because its
  conclusion is under `∀ e : E`.
- For every chosen `e`, the component fiber contains `e`; consequently its
  cardinal is positive.  It is a subtype of the full `n`-element fiber, giving
  the asserted upper bound.
- At `n = 1`, the rank formula is `2 * 1 + 1 = 3`, agreeing with the identity
  cover of the three-circle wedge.

## Definitions

`T99J01ComponentSheets p e` is the cardinality of the points over `p e` that
are joined to `e`.  This is precisely the degree of the cover after restricting
its total space to the path component through `e`.

## Lemmas

### `t99J01_threeCircles_fundamentalGroup` — LIBRARY

**Statement.** At every basepoint `x`, the fundamental group of the concrete
iterated point-wedge `ThreeCircles` is nonempty-equivalent to `FreeGroup (Fin 3)`.

**Why true.** Apply van Kampen twice to the point-wedge model.  The two-circle
piece gives `F₂`; adjoining the final circle gives
`Monoid.Coprod (FreeGroup (Fin 2)) (FreeGroup (Fin 1))`, which is `F₃`.
Transport from the distinguished wedge point to arbitrary `x` using path
connectedness.  The closest sorry-free construction is
`ConstructionTargets/PointWedgeVanKampen.lean`; it already proves the needed
path/local-path topology and most coordinate normalization.  Its ledger STOP
records the exact remaining theorem as
`genericPointWedgeLegCoordinates_vanKampen` (the two middle morphisms after
endpoint transport), followed by the final specialization.  This is genuinely
large shared infrastructure, so it is stated once rather than split into fake
small obligations.

**Estimate.** LIBRARY program, 300–600 lines beyond the banked construction.

**Depends on.** None of the other blueprint lemmas.

**Truth check.** Hand computation by van Kampen gives
`Z * Z * Z = F₃`; the rank at the wedge point and at any transported basepoint
is unchanged.  The topology ledger has compiled the component calculations up
to the explicitly recorded normalization gap.

### `t99J01_exists_connected_cover`

**Statement.** For each positive `n`, there is a path-connected `n`-sheeted
cover of `ThreeCircles`.

**Why true.** Collapse the second and third circle to the wedge point and pull
back the degree-`n` power map on the first circle.  Use the sorry-free files
`CyclicThreeCirclesPullbackCover.lean`,
`CyclicThreeCirclesPullbackSheets.lean`, and
`CyclicThreeCirclesPullbackPathConnected.lean`.  Positivity supplies `NeZero n`.

**Estimate.** 30–50 lines (mostly assembling the three existing declarations).

**Depends on.** Nothing.

**Truth check.** For `n = 1` this is the identity-like pullback.  For general
positive `n`, the first loop cyclically permutes all `n` sheets, so the total
space is connected; each fiber of the power map has exactly `n` points.

### `t99J01_connected_cover_fundamentalGroup`

**Statement.** Assuming the base fundamental-group equivalence, every connected
`n`-sheeted cover has fundamental group `F_(2n+1)` at every point.

**Why true.** The covering-induced map on fundamental groups is injective and
its image has index `n` (`T99J01CoverSubgroupIndex.lean`).  Transport the image
through the supplied `F₃` equivalence, identify the source with that image, and
apply `FiniteIndexFreeGroupSchreierRank.indexSubgroupFreeGroupFinThreeEquiv`.
The positivity required by Schreier follows because a fiber contains the chosen
point and has cardinal `n`.

**Estimate.** 80–140 lines.

**Depends on.** Takes the conclusion of the LIBRARY lemma as an explicit
hypothesis, so it can be developed in parallel.

**Truth check.** Schreier's formula for an index-`n` subgroup of `F_r` is
`n(r-1)+1`; substituting `r=3` gives `2n+1`.  At `n=1` it returns rank three.

### `t99J01_arbitrary_cover_component`

**Statement.** For a chosen point in any finite cover, its path component has
positive degree at most the total degree and ambient fundamental group
`F_(2d+1)`, where `d` is the component sheet count.

**Why true.** Restrict the total space to `{x // Joined e x}`.  The sorry-free
component files `T99J01PathComponentCoverRestriction.lean` and
`T99J01ComponentSheetBounds.lean` establish positivity and the upper bound;
the covering restriction gives a connected `d`-sheeted cover.  Apply the
supplied connected-cover theorem, then use the inclusion of a path component
to identify its based fundamental group with the ambient one.

**Estimate.** 100–150 lines.

**Depends on.** Takes the conclusion of the connected-cover lemma as an
explicit hypothesis, allowing both lemma bodies to be developed in parallel.

**Truth check.** The component fiber contains `e` and injects into the full
fiber.  For a disconnected cover whose degrees form a partition
`n = d₁ + ... + d_k`, the formula gives rank `2dᵢ+1` on component `i`, exactly
the informal answer.

## Dependency layers

- Layer 1 (parallel): `t99J01_threeCircles_fundamentalGroup` (LIBRARY),
  `t99J01_exists_connected_cover`,
  `t99J01_connected_cover_fundamentalGroup`, and
  `t99J01_arbitrary_cover_component`.  The latter two receive earlier
  conclusions as hypotheses and therefore do not need their proofs.
- Layer 2: `apm_t99j01`, a sorry-free three-line assembly.

## Axiom gate

Compilation output is pasted below after the checked build.

```text
'apm_t99j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

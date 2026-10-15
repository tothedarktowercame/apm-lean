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

### Fundamental group split (six parallel leaves)

The banked file `ConstructionTargets/PointWedgeVanKampen.lean` now contains the
actual sorry-free generic equivalence
`genericPointWedgeFundamentalGroupEquiv`; the older ledger description of a
remaining 300--600 line normalization gap is obsolete.  Only concrete
specialization and elementary free-group algebra remain.  The distinguished
point used by every leaf is the explicit definition `T99J01ThreeCirclesPoint`.

#### `t99J01_circle_fundamentalGroup`

**Statement.** `π₁(Circle,1) ≃ FreeGroup (Fin 1)`.

**Proof target.** Compose
`ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt`
with
`ConstructionTargets.PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne`.

**Estimate.** 10--20 lines. **Independent.**

**Truth/degenerate check.** `Fin 1` is inhabited and has exactly one generator;
the multiplicative integer convention agrees with the imported circle
winding-number equivalence, so no inverse/sign choice is introduced here.

#### `t99J01_twoCircles_fundamentalGroup_coprod`

**Statement.** At `twoCirclesPoint`, `π₁(TwoCircles)` is the coproduct of the
two literal circle fundamental groups.

**Proof target.** Specialize
`ConstructionTargets.PointWedgeVanKampen.genericPointWedgeFundamentalGroupEquiv`
with `X = Y = Circle`, `x₀ = y₀ = 1`, and both punctured neighbourhoods equal
to `circleBaseNeighborhood`; discharge the open/member/contraction arguments
using `circleBaseNeighborhood_isOpen`, `circleBase_mem`, and
`circleBaseNeighborhood_contraction`.

**Estimate.** 20--45 lines. **Independent.**

**Truth/degenerate check.** The displayed basepoint unfolds definitionally to
`twoCirclesPoint`; neither wedge leg is empty and both overlap contractions are
pointed at the identified point.

#### `t99J01_twoCircles_fundamentalGroup_freeGroup`

**Statement.** Given the preceding circle and coproduct equivalences as
explicit hypotheses, `π₁(TwoCircles,twoCirclesPoint) ≃ FreeGroup (Fin 2)`.

**Proof target.** Use `MulEquiv.coprodCongr`, then
`PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum`, followed by
`MulEquiv.ofBijective (FreeGroup.map finSumFinEquiv)` with
`FreeGroup.map_injective` and `FreeGroup.map_surjective`.  `norm_num` or
`simpa` resolves `1 + 1 = 2`.

**Estimate.** 25--50 lines. **Independent given its two hypotheses.**

**Truth/degenerate check.** Both input ranks are one; this leaf cannot become
vacuous because its conclusion is a new equivalence, not one of its hypotheses.

#### `t99J01_threeCircles_fundamentalGroup_coprod`

**Statement.** At `T99J01ThreeCirclesPoint`, `π₁(ThreeCircles)` is the coproduct
of the literal based groups of `TwoCircles` and `Circle`.

**Proof target.** Specialize `genericPointWedgeFundamentalGroupEquiv` with
`X = TwoCircles`, `Y = Circle`, `x₀ = twoCirclesPoint`, `y₀ = 1`,
`M = circleBaseNeighborhood`, and `N = twoCirclesBaseNeighborhood`.  Use
`circleBaseNeighborhood_isOpen`, `circleBase_mem`,
`circleBaseNeighborhood_contraction`, `twoCirclesBaseNeighborhood_isOpen`,
`twoCirclesBase_mem`, and `twoCirclesBaseNeighborhood_contraction`.

**Estimate.** 25--55 lines. **Independent.**

**Truth/degenerate check.** `T99J01ThreeCirclesPoint` is definitionally the
left-leg wedgepoint expected by the generic theorem.  Both neighbourhoods
contain their named basepoints.

#### `t99J01_threeCircles_wedgePoint_fundamentalGroup`

**Statement.** Given the circle rank-one, two-circle rank-two, and second
coproduct equivalences as explicit hypotheses, the distinguished three-circle
group is `FreeGroup (Fin 3)`.

**Proof target.** Compose the supplied wedge equivalence with
`MulEquiv.coprodCongr` of the supplied rank-two and rank-one equivalences, then
with `PointWedgeVanKampen.coprodFreeGroupFinTwoFinOne_equiv`.

**Estimate.** 15--30 lines. **Independent given its three hypotheses.**

**Truth/degenerate check.** The ranks are literally `2` and `1`; the final
banked equivalence uses `finSumFinEquiv`, hence lands in `Fin 3` with no hidden
cardinality premise.

#### `t99J01_threeCircles_basepoint_transport`

**Statement.** For arbitrary `x`, the group based at `x` is equivalent to the
group based at `T99J01ThreeCirclesPoint`.

**Proof target.** Use
`FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`; the required
`PathConnectedSpace ThreeCircles` instance is banked as
`PointWedgeVanKampen.threeCircles_pathConnected`/available by inference.

**Estimate.** 5--15 lines. **Independent.**

**Truth/degenerate check.** `ThreeCircles` is nonempty (the explicit wedgepoint
witnesses this) and path connected, so transport exists for every boundary or
wedgepoint choice; no orientation convention affects an abstract equivalence.

#### `t99J01_threeCircles_fundamentalGroup` (assembly, sorry-free)

Obtain the six equivalences above, feed conclusions through the explicit
hypotheses of the two algebra leaves, and compose basepoint transport with the
distinguished-point rank-three equivalence.  This theorem contains no `sorry`.

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

- Layer 1 (parallel): the six fundamental-group leaves above,
  `t99J01_exists_connected_cover`,
  `t99J01_connected_cover_fundamentalGroup`, and
  `t99J01_arbitrary_cover_component`.  The latter two receive earlier
  conclusions as hypotheses and therefore do not need their proofs.
- Layer 2: `t99J01_threeCircles_fundamentalGroup`, a sorry-free assembly.
- Layer 3: `apm_t99j01`, a sorry-free three-line assembly.

## Axiom gate

Compilation output is pasted below after the checked build.

```text
'apm_t99j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

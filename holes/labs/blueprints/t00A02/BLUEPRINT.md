# Blueprint for t00A02

## Triage

Verdict: **true and faithful**.

The registered theorem incorporates the source's necessary convention that the
covering spaces in part (a) are connected: `PathConnectedSpace E₁` and
`PathConnectedSpace E₂` exclude disjoint unions whose component degrees form
different partitions of ten.  The genus hypothesis is now an actual
homeomorphism to `ConstructionTargets.Surfaces.Surface true 5`, matching the
homeomorphism-class language of the source.  The last two conjuncts encode the
literal antipodal quotient and the literal wedge quotient, and regularity is
deck-homeomorphism transitivity on every fibre.

I tried the relevant degeneracies.  The unit sphere contains no zero vector,
so `x` and `-x` are distinct and the already proved fibre cardinality really is
two.  A path-connected degree-ten cover cannot acquire an empty or separate
component.  The two four-point monodromy pairs below are transitive, so their
total spaces are connected.  The regular pair acts simply transitively, while
the irregular pair has inequivalent sheet types over the first summand.  No
counterexample is recorded in the solve-loop ledger or topology audit; their
STOP entries identify missing topology, not a statement defect.

The solve loop's proved quotient-relation classification, surjectivity, exact
fibre cardinality, and Boolean witness eliminators are copied with their proofs.
I searched all sorry-free `ConstructionTargets` files for `cover`, `Surface`,
`wedge`, `homeomorph`, and `Euler`.  The useful existing general input is
`ConstructionTargets.DeckGroupQuotientFundamentalGroup.quotientMk_isCoveringMap`,
so its sorry-free module is imported.  It applies to an orbit quotient and does
not itself identify the custom `EqvGen` quotient used here.  `Surfaces` supplies
the concrete polygon model.  The unfinished `SurfaceClassification` module is
not imported: its current declarations stop at finite disk-cover infrastructure
and it contains `sorry`.

## Remaining lemmas

### `apm_t00A02_antipodalCover_isCoveringMap`

**Statement.** The concrete quotient map from the unit two-sphere by the
generated relation `x ~ -x` is a covering map.

**Why true.** Equip the sphere with the `ZMod 2` antipodal action.  Prove the
action is free using the unit-sphere equation, continuous, and properly
discontinuous (small metric balls about `x` and `-x` are disjoint).  Apply
`ConstructionTargets.DeckGroupQuotientFundamentalGroup.quotientMk_isCoveringMap`.
The already proved `apm_t00A02_antipodal_eqvGen_iff` identifies its orbit
relation with this file's generated relation; transport the covering map across
the induced homeomorphism of quotient spaces.  A direct evenly-covered-ball
proof is an equally short route.

**Expected size.** 60–120 lines.

**Dependencies.** Definitions and the already proved relation lemmas only.

**Truth check.** For every unit vector `x`, `x ≠ -x`; balls of radius less
than half `dist x (-x)` separate the two orbit points.  The proved equivalence
`q x = q y ↔ y = x ∨ y = -x` rules out hidden extra quotient points.

### `apm_t00A02_regular_wedge_cover` — LIBRARY

**Statement.** Assuming the antipodal projection is a covering map, the wedge
has a connected regular four-sheeted cover.

**Why true.** Use fibre `{1,2,3,4}` and involutions
`a = (12)(34)`, `b = (13)(24)`.  Glue two antipodal sphere covers over each
summand along the four points over the wedge point.  Quotient gluing charts give
a four-sheeted covering.  The generated Klein four group acts transitively by
deck homeomorphisms, hence satisfies `apm_t00A02_isRegularCover`.

The closest sorry-free infrastructure is the imported deck-group quotient
module, but no sorry-free module constructs a cover of a quotient wedge from
finite monodromy or proves the necessary gluing theorem.  Thus the concrete
wedge gluing is the missing library-sized content.

**Expected size.** 150–250 lines (or a short adapter after a monodromy-cover
construction is supplied).

**Dependencies.** Takes the exact conclusion of
`apm_t00A02_antipodalCover_isCoveringMap` as `hanti`, so a separate seat can
work with that interface immediately.

**Truth check.** Both involutions are fixed-point-free and their generated
orbit from `1` is all four points.  They commute, and the four generated
permutations act freely and transitively, giving regularity.

### `apm_t00A02_irregular_wedge_cover` — LIBRARY

**Statement.** Assuming the antipodal projection is a covering map, the wedge
has a connected nonregular four-sheeted cover.

**Why true.** Use `a = (12)` (fixing `3,4`) and
`b = (14)(23)`.  Over the first projective-plane summand glue one antipodal
sphere and two identity projective-plane sheets; over the second glue two
antipodal spheres.  The action is transitive, hence the total space is
connected.  Any deck map must preserve the isomorphism type of the lobe above
the first summand, so it cannot carry sheet `1` to sheet `3`; deck transitivity
fails.

As in the regular case, the absent ingredient is a general finite-monodromy
wedge-cover gluing API.  Keeping the two constructions separate prevents two
seats from sharing hidden proof obligations beyond the explicit `hanti`
interface.

**Expected size.** 150–250 lines.

**Dependencies.** Takes the antipodal covering conclusion explicitly.

**Truth check.** Starting at `1`, the two involutions reach `2`, `4`, and then
`3`, so the action is transitive.  The first involution has both a two-cycle and
fixed points, making its sphere and projective-plane lobes visibly inequivalent;
therefore the deck action is not transitive.

### `apm_t00A02_connected_ten_cover_homeomorph` — LIBRARY

**Statement.** Any two path-connected ten-sheeted covers of a surface
homeomorphic to the standard orientable genus-five surface have homeomorphic
total spaces.

**Why true.** A finite cover of a closed orientable surface is again a closed
orientable surface, and Euler characteristic multiplies by the number of
sheets.  Since `χ(Σ₅) = 2 - 2·5 = -8`, each degree-ten cover has
characteristic `-80`, hence genus `41`.  Surface classification identifies
both total spaces with `Surface true 41`, and composing the equivalences gives
the conclusion.

This is the shared surface-classification foundation program named
`ConstructionTargets.SurfaceClassification` in the topology worklist.  Its
current sorry-free progress constructs finite closed-disk covers but has not
yet delivered finite-cover Euler multiplicativity or the classification
theorem.  The statement here is the consumer-specialized final interface;
splitting it into small lemmas would only disguise that program-sized gap.

**Expected size.** A sub-100-line adapter after the shared foundation; the
foundation itself is estimated at 1,500–3,000 lines.

**Dependencies.** None within this blueprint.

**Truth check.** Hand computation gives
`10(2 - 2·5) = -80 = 2 - 2·41`.  Connectedness is essential: without it,
different degree partitions yield nonhomeomorphic disconnected total spaces,
and the formal hypotheses correctly exclude that case.

## Assembly and dependency layers

The main theorem uses the classification lemma for its first conjunct, pairs
the antipodal covering lemma with the already proved fibre-cardinality lemma,
and constructs both wedge witnesses from the two dedicated lemmas.  Its type
is identical to `problems/t00A02/lean/Main.lean`, and it has no direct `sorry`.

- **Layer 1 (parallel):** `apm_t00A02_antipodalCover_isCoveringMap` and
  `apm_t00A02_connected_ten_cover_homeomorph`.
- **Layer 2 mathematically, but assignable in parallel with Layer 1:**
  `apm_t00A02_regular_wedge_cover` and
  `apm_t00A02_irregular_wedge_cover`; each receives Layer 1's conclusion as an
  explicit hypothesis and can therefore be proved in an isolated seat.
- **Layer 3 (already compiled):** `apm_t00a02` assembly.

There are four admitted lemmas.  The two wedge lemmas and surface
classification lemma are marked LIBRARY because the missing reusable topology
exceeds a single 30–150-line consumer proof.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00A02/Blueprint.lean
```

The output of `#print axioms apm_t00a02` was:

```text
'apm_t00a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The four warnings identifying `sorry` are exactly the four remaining lemmas;
the main theorem contains no direct `sorry`.

# t03J03 blueprint

## Triage

Verdict: **true and faithful**. The batch registration already records the
statement as faithful, and the frozen Lean theorem expresses both parts of
`problem.md`: all double covers (seven connected character covers plus the
disconnected trivial cover), followed by lifting every embedded closed
cylinder to an orientable double cover.

I tried the relevant edge cases. The zero character is deliberately absent
from `apm_t03J03_character`; it corresponds to the separately listed
disconnected trivial cover. There are `2^3 - 1 = 7` nonzero characters, which
the compiled `native_decide` proof confirms. The all-ones orientation
character is nonzero. An orientable disconnected cover cannot be a hidden
exception: the trivial cover has two copies of the nonorientable base. At the
cylinder endpoints `0` and `1`, the closed annulus is still connected and its
core remains two-sided; no boundary-radius degeneration changes the lifting
argument.

The hand check is the classical one. Connected double covers of `N₃` are
classified by the seven nonzero maps `π₁(N₃) → Z/2`. The all-ones map
is the orientation character, giving `Σ₂`; the other six covers give `N₄`.
The zero map gives `N₃ ⊔ N₃`. An embedded annulus has a two-sided core,
so its orientation character vanishes and the map lifts to the orientation
cover.

## Shared definitions and completed facts

All definitions and the theorem type are copied verbatim from
`problems/t03J03/lean/Main.lean`. The three Euler-characteristic equalities,
the cardinality-seven computation, nonzeroness of the orientation character,
and `apm_t03J03_exists_cylinderLift_of_range_le` are already proved. The last
of these is a direct wrapper around
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`; it leaves only
the geometric orientation-range argument.

I searched every sorry-free `ConstructionTargets/*.lean` (using
`grep -L sorry`) for double-cover, covering, polygon-surface, orientation, and
surface-model results. The closest relevant modules are
`ConstructionTargets/Surfaces.lean`,
`ConstructionTargets/PolygonSurfacePiOne.lean`,
`ConstructionTargets/DeckGroupQuotientFundamentalGroup.lean`, and the general
covering/path-component modules. None constructs the seven covers, proves the
required polygon normal-form homeomorphisms, or proves the two-sided-annulus
orientation result. `PolygonSurfaceHomology` is still only a program/blueprint
on this branch, while `SurfaceClassification.lean` does not yet expose a
closed-surface classification theorem usable here. Therefore the remaining
large steps are honestly marked LIBRARY rather than split into fake adapters.

## Lemmas

### `apm_t03J03_connected_double_cover_classification` — LIBRARY

**Statement.** There are seven actual connected double-cover representatives
indexed by nonzero `Fin 3 → ZMod 2` characters; every connected double cover is
equivalent over `N₃` to exactly one; the all-ones representative has total
space `Σ₂`, and every other representative has total space `N₄`.

**Why true.** Trivialize a pulled-back cover over the polygon disk, record the
sheet swap on each of the three paired crosscap edges, and descend. Nonzero
labels are precisely the connected covers. Equivalence over the base preserves
monodromy, giving uniqueness. Polygon cut-and-paste identifies the all-ones
word with the orientable genus-two polygon and the other six with a four-
crosscap polygon. This is the worklist chain
`DiskCoverTrivialization.trivialize` →
`PolygonCoverDescent.classifyLabels` →
`PolygonCoverNormalForm.doubleCoverModels`.

**Estimate.** 700–1,200 lines total across that registered library program;
the final adapter to this exact existential is 30–80 lines.

**Dependencies.** None among blueprint lemmas.

**Truth check.** Explicitly enumerating `(Z/2)^3` gives one zero label and
seven nonzero labels. Euler characteristic doubles from `-1` to `-2`, leaving
exactly `Σ₂` or `N₄`; the orientation character selects the former.

### `apm_t03J03_disconnected_double_cover_trivial` — LIBRARY

**Statement.** Every disconnected exact two-sheeted cover of `N₃` is
homeomorphic over the base to `N₃ ⊕ N₃ → N₃`.

**Why true.** Since the base is connected, every component of a covering has
constant positive sheet number. Two total sheets and at least two components
force exactly two one-sheet components. A one-sheet covering is a
homeomorphism, and the two inverse homeomorphisms assemble into the required
sum homeomorphism. The closest sorry-free infrastructure is
`CoveringPathComponentDomain`, `CoveringPathComponentSurjective`, and
`CoveringRetainedSheetHomeomorph`, but no theorem currently packages this
arbitrary-topology conclusion.

**Estimate.** 120–220 lines.

**Dependencies.** None.

**Truth check.** A fibre has cardinality exactly two. Thus three nonempty
covering components are impossible, while a single component contradicts the
hypothesis; each of the two components must contribute exactly one point to
each fibre.

### `apm_t03J03_orientable_double_cover_annulus_lift` — LIBRARY

**Statement.** Assuming the complete connected-cover classification
interface, every embedded closed cylinder in `N₃` lifts to every orientable
double cover.

**Why true.** Orientability excludes the disconnected trivial cover. The
classification hypothesis then identifies the cover with the all-ones
orientation cover. Restrict the embedding to a core circle. Its annular
neighborhood makes it two-sided, hence orientation-preserving; therefore its
fundamental-group image lies in the kernel of the orientation character.
The cylinder retracts to that core, so the whole induced range lies in the
cover subgroup. Choose a point in the two-element fibre and apply the already
proved `apm_t03J03_exists_cylinderLift_of_range_le`. This is the worklist's
`SurfaceOrientation.twoSidedAnnulusLifts` program boundary.

**Estimate.** 300–500 lines of missing surface-orientation library work, then
30–60 lines of lifting assembly.

**Dependencies.** It takes the full conclusion of
`apm_t03J03_connected_double_cover_classification` as a hypothesis, so its
seat can work in parallel without invoking that unfinished lemma.

**Truth check.** The core `S¹ × {1/2}` has the explicit two-sided neighborhood
`S¹ × (1/2-ε,1/2+ε)`. By contrast, a Möbius-band core is one-sided and
would fail the orientation-kernel test, confirming that the embedding and
cylinder hypotheses are doing real work.

## Dependency layers

- Layer 1 (parallel):
  `apm_t03J03_connected_double_cover_classification` (LIBRARY),
  `apm_t03J03_disconnected_double_cover_trivial` (LIBRARY), and
  `apm_t03J03_orientable_double_cover_annulus_lift` (LIBRARY, developed
  against the classification conclusion supplied as an explicit hypothesis).
- Layer 2: instantiate the annulus-lift lemma with the completed
  classification lemma and assemble `apm_t03j03`; this assembly is already
  sorry-free.

There are three unfinished top-level lemmas, all marked LIBRARY. I am
convinced their statements are true. The doubt is implementation scale: the
literal polygon-cover normal-form homeomorphisms and local orientation theory
are not present in the current sorry-free library.

## Compile and axiom gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t03J03/Blueprint.lean
```

Output of `#print axioms apm_t03j03`:

```text
'apm_t03j03' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 apm_t03J03_character_card._native.native_decide.ax_1_1]
```

The main theorem contains no `sorry`; `sorryAx` enters only through the three
named LIBRARY lemmas.

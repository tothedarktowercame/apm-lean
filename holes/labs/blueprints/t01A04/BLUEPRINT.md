# Blueprint for t01A04

## Triage

Verdict: **true and faithful**.  No statement repair is needed.

The source asks for the presentation of `T² ∨ S¹` and two index-two
subgroups with nonisomorphic covers.  The Lean theorem gives the standard
presentation by three generators `a,b,c` with the sole relation `ab = ba`,
the two parity characters `(0,0,1)` and `(1,0,0)`, their concrete covering
maps and induced subgroup ranges, and nonhomeomorphism of the concrete total
spaces.  This is stronger in explicit data but does not change the problem.

Degenerate checks: the source space is nonempty and its chosen basepoint is
defined; both characters send one displayed generator to the nonidentity of
`Multiplicative (ZMod 2)`, hence are surjective rather than accidentally
trivial; the two kernels differ because `a` and `c` receive opposite parity;
and the two total spaces have respectively two and one torus components after
cutting away the attached one-dimensional pieces.  The solve-loop and topology
records contain no counterexample.  Their reviewed STOP is an API/foundation
gap: no existing theorem turns these EqvGen quotient gluings into covers.

All definitions and proved quotient-map infrastructure from `Main.lean` are
copied unchanged.  In particular, the raw maps respect the generated
relations, descend continuously, preserve basepoints, and are surjective.

## Remaining lemmas

### Covering-map leaves (four independent seats)

* `apm_t01A04_circleCoverMap_evenlyCovered_away` (80–130 lines): construct an
  evenly covered neighborhood of every non-wedge point.  On a torus
  representative use a neighborhood avoiding `(1,1)` and two identity
  sheets; on a circle representative use
  `Circle.isQuotientCoveringMap_npow 2`, shrinking away from `1` when needed.
* `apm_t01A04_circleCoverMap_evenlyCovered_basepoint` (100–150 lines): take a
  small arc `U` about `1` with its two inverse arcs under squaring and glue the
  corresponding small torus neighborhoods to those arcs in each sheet.
* `apm_t01A04_torusCoverMap_evenlyCovered_away` (80–130 lines): the analogous
  non-wedge construction, using circle squaring in the first torus coordinate
  and two identity copies on the attached circle.
* `apm_t01A04_torusCoverMap_evenlyCovered_basepoint` (100–150 lines): use the
  two inverse product neighborhoods near `(1,1)` and `(-1,1)`, glued to the
  matching neighborhoods in the two attached circles.

All four statements use Mathlib's native
`IsEvenlyCovered f x (f ⁻¹' {x})`, so they are independently provable and no
leaf imports another leaf's `sorry`.  Useful API: the definition of
`IsEvenlyCovered`, `IsEvenlyCovered.of_openPartialHomeomorph`,
`IsEvenlyCovered.reindex`, `Circle.isQuotientCoveringMap_npow`,
`IsCoveringMap.isEvenlyCovered`, `Homeomorph.prodCongr`,
`isQuotientMap_quotient_mk'.isOpen_preimage`, and
`Topology.IsQuotientMap.continuous_iff`.  The most direct proof is to give the
open set and homeomorphism required by `IsEvenlyCovered`; quotient equality is
handled by induction on `Relation.EqvGen`.

Degenerate check: the away hypotheses exclude the only point at which the two
summands meet.  The basepoint fibers have exactly two points, not one: the
attachment identifies within each sheet but never identifies the two sheets.
The inverse arcs must be chosen disjoint (including their endpoints), so no
branching is hidden at `1` or `-1`.

`apm_t01A04_bridge_quotient_maps_are_coverings` is now a sorry-free 12-line
assembly: split on `x = apm_t01a04_basepoint` and apply the relevant local
leaf.

### Canonical loops, presentation, parity, and ranges

The definitions `apm_t01A04_loopA`, `apm_t01A04_loopB`, and
`apm_t01A04_loopC` are sorry-free.  They are the FundamentalGroup classes of
explicit paths: one positive `integerLoop` in respectively the first torus
coordinate, second torus coordinate, and extra circle.  The last path is cast
at both endpoints using the defining wedge relation.  Thus none of the range
claims quantifies over a replaceable abstract generating triple.

* `apm_t01A04_canonical_loops_presentation` (100–150 lines, independent):
  prove that these particular loops commute in the first two entries, generate,
  and satisfy the displayed universal property.  Compare the concrete EqvGen
  relation with `ConstructionTargets.PointWedgeQuotient.Rel` using
  `quotientHomeomorphOfRelIff`, then use
  `ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeFundamentalGroupMulEquiv`.
  The key remaining naturality computation sends the explicit `integerLoop`
  paths to `Monoid.Coprod.inl (Multiplicative.ofAdd (1,0))`,
  `Monoid.Coprod.inl (Multiplicative.ofAdd (0,1))`, and
  `Monoid.Coprod.inr (Multiplicative.ofAdd 1)`.  Finish with
  `Monoid.Coprod.lift`, `MonoidHom.ext`, and `Subgroup.closure_eq_top`.
* `apm_t01A04_canonical_parity_characters` (40–80 lines, independent given
  its explicit universal-property hypothesis): instantiate that hypothesis
  twice with values `(0,0,1)` and `(1,0,0)`.  Use `ZMod.eq_zero_or_eq_one`,
  `Subgroup.index_ker`, and `SetLike.ext'` (or distinguish the kernels on
  `loopA`/`loopC`) for surjectivity, index two, and inequality.
* `apm_t01A04_circleCoverMap_range_eq_parity_kernel` (80–140 lines): given
  values on the canonical loops and an explicit `IsCoveringMap` hypothesis,
  compute lifted endpoints.  `loopA` and `loopB` have closed lifts in torus
  sheet zero, while `loopC` lifts along circle squaring from `1` to `-1` and
  is not closed.  Use `IsCoveringMap.monodromy`,
  `IsCoveringMap.monodromy_trans_apply`, `FundamentalGroup.toPath`, and the
  lift/range criterion developed in
  `ConstructionTargets.DeckGroupQuotientFundamentalGroup`.
* `apm_t01A04_torusCoverMap_range_eq_parity_kernel` (80–140 lines): the same
  argument with `loopA` lifting under first-coordinate squaring from `1` to
  `-1`, while `loopB` stays closed in the torus and `loopC` stays closed in
  attached circle sheet zero.

The two range leaves take `IsCoveringMap` as an explicit hypothesis; hence
they can be proved before any covering leaf lands.  They also take generator
values and the closure statement for the three fixed loops.  Replacing a
generator by (for example) `loopA * loopC` is therefore impossible; this is
the defect in the previous statements.  The range leaves, presentation leaf,
and parity leaf have no sorry-dependency on one another because every needed
conclusion is passed as an explicit hypothesis.

Truth check: abelianization is `ℤ³`; the characters are the nonzero forms
`(0,0,1)` and `(1,0,0)`.  Their kernels therefore have index two and differ.
For a connected two-sheet cover, the induced fundamental-group range is the
stabilizer of the chosen sheet; in a two-point fiber that stabilizer is exactly
the kernel of the computed parity character.  There are no empty-fiber or
dimension-zero cases because both maps are already proved surjective and both
basepoint fibers are inhabited.

`apm_t01A04_bridge_piOne_presentation_and_ranges` is now a sorry-free
assembly.  It obtains the two covering hypotheses from the first bridge and
passes them explicitly to the two range leaves.

### `apm_t01A04_bridge_total_spaces_not_homeomorphic` — LIBRARY

**Statement.** The two explicit quotient total spaces are not homeomorphic.

**Why true.** Compute singular `H₂`.  Point attachment of circles does not add
degree-two homology.  The first total space contains two torus copies and has
`H₂ ≅ ℤ²`; the second contains one torus and has `H₂ ≅ ℤ`.  A
homeomorphism would induce an isomorphism between these groups, impossible.
An elementary alternative is a cut-point/component-count argument, but the
homology proof matches the informal solution and is less sensitive to a
case-heavy quotient point analysis.

**Expected size.** 200–350 lines.  Marked LIBRARY because the missing useful
result is point-wedge homology (or the corresponding Mayer–Vietoris theorem),
not several artificial restatements of this same calculation.

**Dependencies.** Definitions and proved lemmas in this file only.

**Truth check.** Collapsing/ignoring the attached one-dimensional graph leaves
two independent oriented torus fundamental classes in the circle-doubled
space and one in the torus-doubled space.  Tensoring with `ZMod 2` gives ranks
two and one as a second check, so torsion cannot obscure the distinction.

## Search and imported foundations

I searched every sorry-free `ConstructionTargets/*.lean` module for wedge,
Van Kampen, quotient-covering, and singular-homology results.  The closest
usable modules are imported directly in `Blueprint.lean`:

* `ConstructionTargets.GenericTargetNaturalSourceReconstruction`, whose
  `wedgeFundamentalGroupMulEquiv` computes the abstract torus-circle wedge;
* `ConstructionTargets.DeckGroupQuotientFundamentalGroup`, which supplies
  quotient-covering and lifting machinery.

Neither proves the concrete EqvGen gluing is a cover, the needed naturality on
the three concrete loops, nor point-wedge `H₂`.  No `SphereCap*` module is
imported.  Both imported files are sorry-free.

## Dependency layers

* **Layer 1 (parallel):** the four evenly-covered leaves, canonical-loop
  presentation leaf, parity-character leaf (with the universal property as an
  input), the two range leaves (with closure, values, and covering as inputs),
  and the unchanged total-space nonhomeomorphism leaf.  All nine seats are
  independent.
* **Layer 2 (sorry-free):** the two named bridge lemmas assemble the first
  seven leaves.
* **Layer 3 (already proved):** `apm_t01a04` destructures the bridge data,
  selects the concrete maps, and adds the nonhomeomorphism leaf.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A04/Blueprint.lean
```

The warnings identify exactly the eight revised leaf lemmas plus the unchanged
total-space nonhomeomorphism lemma.  Both requested bridge lemmas are
sorry-free.  The final
output of `#print axioms apm_t01a04` is:

```text
'apm_t01a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus the main theorem has no direct `sorry`; `sorryAx` reaches it only through
the eight isolated leaves above.

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

### `apm_t01A04_bridge_quotient_maps_are_coverings` — LIBRARY

**Statement.** Both explicit quotient maps are covering maps.

**Why true.** Away from the glued points this is the disjoint union of copies
of an identity map and the standard circle squaring cover.  At the wedge point,
choose small product/circle arcs evenly covered by squaring.  Their copies in
the source quotient are disjoint open sheets and each maps homeomorphically to
the corresponding wedged neighborhood.  This is precisely the missing
EqvGen-quotient covering-gluing theorem recorded by the topology loop.
Surjectivity is already proved by
`apm_t01a04_circleCoverMap_surjective` and
`apm_t01a04_torusCoverMap_surjective`.

**Expected size.** 200–400 lines.  This is marked LIBRARY rather than split
into fake local lemmas: the reusable deliverable should be a general
point-wedge covering-gluing theorem (also useful to t00A02, t92J06, t97A03,
and t98A03), followed by a short specialization.

**Dependencies.** Definitions and proved lemmas in this file only.

**Truth check.** Over the wedge point each map has exactly two preimages.  For
the circle-doubled cover these are the attachment points on the doubled circle;
for the torus-doubled cover they are `(1,1)` and `(-1,1)` on the doubled first
torus coordinate.  Circle squaring has two disjoint local inverse arcs at
those points, so the gluing creates no branching.

### `apm_t01A04_bridge_piOne_presentation_and_ranges`

**Statement.** The concrete fundamental group has generators `a,b,c` with
the universal presentation `⟨a,b,c | ab=ba⟩`; the two parity characters
have the displayed values, are onto with distinct index-two kernels, and the
two concrete induced maps have exactly those ranges.

**Why true.** Transport
`ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeFundamentalGroupMulEquiv`
across the definitional/homeomorphic identification of the local quotient
`apm_t01a04_X` with its `GenericWedge`.  The free-product injections give `a`,
`b`, and `c`; the universal property of `Monoid.Coprod` proves the displayed
mapping property and defines the two maps to `ZMod 2`.  Kernel index is two by
surjectivity.  For the range clauses, compute monodromy: the first cover flips
sheets exactly on `c`, and the second exactly on `a`.  The standard lifting
criterion says that a loop lies in the induced range iff its monodromy fixes
the chosen sheet.  `ConstructionTargets.DeckGroupQuotientFundamentalGroup`
contains the closest sorry-free quotient-cover/fundamental-group machinery,
but not this point-wedge specialization.

**Expected size.** 120–220 lines after the concrete inclusion naturality and
two-sheet monodromy API are available.  The audit separates those reusable
foundations as `apm_t01a04_piOneEquiv_inclusions` and
`two_sheet_monodromy_character_range`; this exact bridge is the bounded
consumer adapter.

**Dependencies.** Definitions and proved lemmas in this file.  It does not
take the preceding covering proof as a Lean hypothesis, so the two seats can
run in parallel; its proof may establish the required local lifting facts or
use the shared covering-gluing result once banked.

**Truth check.** Abelianizing the presentation gives `ℤ³`; the two characters
are the distinct nonzero linear forms selecting the `c` and `a` coordinates.
Thus each has quotient of order two.  Direct path lifting of the three
generator loops yields monodromy `(0,0,1)` and `(1,0,0)`, exactly matching the
claimed kernels.

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

* **Layer 1 (parallel):** all three remaining lemmas.  Their statements are
  closed over the definitions block and none mentions another lemma's local
  proof data.
* **Layer 2 (already proved):** `apm_t01a04` destructures the presentation data,
  selects the two concrete maps, and combines the three Layer 1 results.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01A04/Blueprint.lean
```

The warnings identify exactly the three top-level admitted lemmas.  The final
output of `#print axioms apm_t01a04` is:

```text
'apm_t01a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus the main theorem has no direct `sorry`; `sorryAx` reaches it only through
the three isolated obligations above.

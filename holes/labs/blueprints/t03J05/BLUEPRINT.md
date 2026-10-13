# Blueprint for t03J05

## Triage and repair

Verdict: **the registered statement is false** and needs the repair in
`RevisedMain.lean`.

There are two defects.

1. Part (b) quantifies over every Mathlib smooth four-manifold, but Mathlib's
   `IsManifold` does not imply Hausdorffness.  Given any proposed curves, glue
   separate copies of `ℝ⁴` to neighbourhoods of two of their product tori.
   The resulting non-Hausdorff locally Euclidean smooth space contains
   `F* × F*` openly, while the two tori factor through contractible copies of
   `ℝ⁴`; hence they are homotopic there.  This is the counterexample recorded
   by `holes/labs/statement-registry/triage-2.md`.  The smallest repair is the
   added instance hypothesis `[T2Space X]`.

2. Part (a) of `problem.md` asks for nonzero intersection *number*.  The old
   Lean theorem only counted points of a set-theoretic intersection.  Two
   embedded curves can touch tangentially at exactly one point, so odd
   cardinality alone does not express the requested invariant.  The repaired
   theorem additionally requires `apm_t03J05_IsSingleTransverseCrossing A₁ B₁`.
   This predicate says that the curves meet at exactly one point and that a
   neighbourhood chart sends their images to the two coordinate axes.  It is
   geometric local data, not the intersection-number conclusion in disguise.

These are the only statement changes.  The Euler characteristic, literal
`Surface true 2`, puncture, four curves, product maps, actual image-cardinality
claim, and universal ambient nonhomotopy conclusion are retained.  The
grader's non-Hausdorff counterexample is excluded by `T2Space`, and the
tangency counterexample is excluded by the coordinate-axis clause.

Degenerate checks: the unique-crossing equality rules out empty curve images
and multiple intersections; the coordinate-axis condition rules out a
tangency at that point.  `Circle` is nonempty, and each embedding therefore
has nonempty image.  The four cross-handle disjointness fields in
`apm_t03J05_CurveSystem` ensure that the three diagonal product tori have the
intended mod-two intersection matrix rather than merely distinct names.

## Definitions

`apm_t03J05_IsSingleTransverseCrossing a b` is the repaired local crossing
condition.  `apm_t03J05_CurveSystem` packages four embedded punctured-surface
curves, transverse crossings `aᵢ` with `bᵢ`, and disjointness between the two
handles.  It contains only geometric input used by intersection theory; it
does not mention homotopy or assert the conclusion of either missing lemma.

The Euler calculation, preservation of embedding under unpuncturing, product
embedding, product-image intersection identity, and parity calculation are
proved without `sorry` in `Blueprint.lean`, reusing the compiled work from the
solve loop.

## Lemmas

### `apm_t03J05_genusTwo_curve_system` — LIBRARY

**Statement in words.** The concrete polygon quotient `Surface true 2` has a
puncture and four embedded circles forming the usual two-handle symplectic
curve system, with each `aᵢ,bᵢ` pair crossing once in coordinate-axis form and
curves on different handles disjoint.

**Why true.** Use the interior of the standard genus-two polygon before edge
identification.  Choose the four standard handle curves away from all vertices
and choose the puncture outside them.  Their compact images lie in quotient
charts on which the quotient map is injective.  The two crossings are ordinary
horizontal/vertical crossings; restricting and rescaling those quotient
charts supplies the homeomorphisms in
`apm_t03J05_IsSingleTransverseCrossing`.  Compact-to-Hausdorff injectivity gives
the four circle embeddings.

**Repository boundary.** `ConstructionTargets.Surfaces` provides the literal
polygon quotient but no explicit embedded basis curves.  The closest planned
surface infrastructure is `ConstructionTargets.PolygonSurfacePiOne` and
`ConstructionTargets.PolygonSurfaceHomology`; neither currently constructs
these geometric circle parametrizations.  This should be developed as the
polygon-surface curve-geometry program rather than postulated separately for
each curve.

**Expected size.** 500–1,200 lines (LIBRARY scale).

**Dependencies.** None within the blueprint.

**Truth check.** In the standard octagon model, horizontal and vertical core
curves for each handle meet once, and curves supported in different handle
bands are disjoint.  Moving the puncture into the complement leaves all four
maps unchanged.  The same construction on a one-handle square gives the
familiar meridian/longitude crossing on a torus.

### `apm_t03J05_curve_system_ambient_separation` — LIBRARY

**Statement in words.** Any curve system with the preceding geometric data
produces three embedded diagonal product tori which remain pairwise
nonhomotopic after every open embedding into a Hausdorff boundaryless smooth
four-manifold.

**Why true.** Over `ZMod 2`, form the product fundamental classes of the four
curves.  The transverse/disjoint pattern gives the intersection table

`a₁²·b₁² = 1`, `b₁²·a₁² = 1`, `a₂²·b₂² = 1`,

with all cross-handle entries zero.  Each compact test torus is closed in the
Hausdorff ambient space.  Excision/localization identifies its local
intersection class in the ambient manifold with the one computed inside the
open subset.  Homotopic maps induce the same degree-two homology class and
hence have equal pairings with every test torus.  The three distinct rows of
the table therefore rule out every pairwise homotopy.

**Repository boundary.** This is the large missing product/intersection
theory theorem identified by the topology loop.  Its current STOP says that
Mathlib and the sorry-free bank contain no singular-chain cross product or
Eilenberg–Zilber comparison.  The active predecessor is the bounded signed
product-simplex shuffle program (total degree at most four), followed by the
bounded singular cross-product interface.  The closest sorry-free local
infrastructure is the existing low-degree singular-cap and local-intersection
work, but it cannot yet produce product fundamental classes.  This lemma is
therefore intentionally stated once as a LIBRARY result, not fragmented into
fake adapters.

**Expected size.** 1,500–4,000 lines across the signed-shuffle, cross-product,
localization/excision, and final intersection-table modules.

**Dependencies.** It takes the conclusion of
`apm_t03J05_genusTwo_curve_system` as an explicit hypothesis.  Thus a lemma
seat can prove it independently for an arbitrary supplied system; it does not
depend on the proof of the construction lemma.

**Truth check.** The hand calculation gives the diagonal `3 × 3` mod-two
intersection matrix.  In the model ambient `F* × F*`, the classes are visibly
distinct.  Compactness plus Hausdorffness makes each test torus closed, exactly
the condition that fails in the recorded non-Hausdorff counterexample.  Empty
and constant-map degeneracies are excluded by the four embedding fields and
the two single-crossing fields.

## Dependency layers

* **Layer 1, parallel LIBRARY programs:**
  `apm_t03J05_genusTwo_curve_system` and
  `apm_t03J05_curve_system_ambient_separation` (the latter is proved
  parametrically from a supplied `CurveSystem`).
* **Layer 2, already compiled:** the main theorem instantiates the ambient
  lemma with the constructed system and assembles the proved embedding and
  odd-cardinality lemmas.

There are **two admitted lemmas**.  Both are genuine library-scale boundaries;
all consumer assembly is sorry-free.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t03J05/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t03J05/Blueprint.lean
```

The output of `#print axioms apm_t03j05` was:

```text
'apm_t03j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` enters only through the two named LIBRARY lemmas; the main theorem
has no direct `sorry`.

# Blueprint for t01J01

## Triage

Verdict: **true and faithful**.

The registered theorem says exactly that two disjoint embedded circles on the
standard closed orientable genus-two surface, each zero on integral first
singular homology but not null-homotopic, cobound a subset homeomorphic to
`Circle × I` whose frontier is their two images.  This matches `problem.md`.

I checked the usual degeneracies.  A space homeomorphic to the standard
genus-two polygon surface is nonempty and is the intended homeomorphism class,
so the empty and zero-space failures do not occur.  An embedding of `Circle`
cannot be constant.  Image-level `Disjoint` rules out coincident curves.
Finally, the non-null-homotopy hypotheses exclude the disk-bounding branch in
the surface-cutting argument.  The endpoints of `Icc 0 1` are distinct, so the
annulus model does not collapse.  The solve-loop and topology ledgers record no
counterexample; they consistently identify missing surface cutting and
classification infrastructure.

The elementary witness-consequence lemmas in `Main.lean` (closedness,
compactness, containment of the boundary ranges, and properness) were checked,
but are not dependencies of the forward construction and therefore are not
copied into the blueprint.

## Remaining lemmas

### `apm_t01J01_nullHomologySeparates` — LIBRARY

**Statement in words.** An embedded circle whose induced map on integral
first singular homology is zero separates the closed orientable genus-two
surface; separation is expressed by non-preconnectedness of its complement.

**Why true.** For a two-sided embedded circle in a closed orientable surface,
nonseparation supplies a transverse closed curve with algebraic intersection
number one.  Its intersection pairing with the embedded circle therefore
detects a nonzero homology class, contradicting the zero induced homology map.
Equivalently, one can prove the result by a collar and the Mayer–Vietoris or
relative-homology sequence.  The large missing ingredients are tameness/a
two-sided annular collar and the surface intersection pairing.

**Expected size.** 500–900 lines as a reusable library programme (the audit
estimates 500+ lines for the collar and 200–400 for the separation argument).

**Dependencies.** Definitions only at the blueprint level.  Internally it is
expected to depend on the shared embedded-circle collar/Schoenflies foundation.

**Truth check.** On the standard genus-two octagon, a nonseparating generator
circle has a dual generator intersecting it once and hence is not
null-homologous.  A separating waist circle is the oriented boundary of either
side and hence is null-homologous.  A contractible embedded circle also
separates, so the lemma correctly does not require essentiality.

**Repository search.** I searched all sorry-free `ConstructionTargets` modules
for `Surface`, `Circle`, `Collar`, `Schoenflies`, `Intersection`,
`nullHomologySeparates`, and `separatingCurvesCoboundAnnulus`.  The closest
modules are `ConstructionTargets.SurfaceSchoenflies`,
`ConstructionTargets.OrientedSurfacePreimageDuality`, and
`ConstructionTargets.SurfaceClassification`; none proves this bridge.

### `apm_t01J01_separatingCurvesCoboundAnnulus` — LIBRARY

**Statement in words.** Two disjoint essential separating embedded circles in
a closed orientable genus-two surface cobound a closed annular subset whose
frontier is exactly their two images.

**Why true.** Cut along the first circle.  Essentiality excludes a disk side;
Euler characteristic and genus two force both sides to be once-holed tori.
The disjoint second circle lies in one side and separates it.  Cutting that
once-holed torus along the second circle gives either a disk plus a once-holed
torus or an annulus plus a once-holed torus.  Essentiality excludes the disk,
leaving the annulus adjacent to the original boundary.  Collar and gluing
bookkeeping produces the literal subset and proves the exact frontier equality.

**Expected size.** 700–1500 lines as a reusable compact-surface cutting and
classification programme.  This intentionally remains one LIBRARY obligation:
the missing cutting object, Euler-characteristic bookkeeping, one-holed-torus
classification, and frontier realization are one shared foundation rather
than independently seat-sized lemmas in the current API.

**Dependencies.** Definitions plus the two separation conclusions supplied as
hypotheses.  Thus it does not depend formally on
`apm_t01J01_nullHomologySeparates` and the two library programmes can run in
parallel.  Internally it should use the shared surface-classification and
embedded-circle-collar foundations.

**Truth check.** Genus bookkeeping gives `g₁ + g₂ = 2` after the first cut;
neither side has genus zero, so the only possibility is `(1,1)`.  In the
once-holed torus, the second cut gives genera summing to one.  The `(1,0)`
branch makes the one-boundary component a disk and contradicts non-null-
homotopy; `(0,1)` makes the component between the two curves an annulus.  This
also checks that both essentiality hypotheses are needed.

**Repository search.** The sorry-free
`ConstructionTargets.SurfaceClassification` module is imported and is the
closest shared programme, but currently ends at finite triangulation and
general-position infrastructure.  No sorry-free module contains a cutting
operation, Euler characteristic under cutting, classification of surfaces
with boundary, or an exact annular-subset/frontier theorem.  The topology
ledger names the intended eventual result
`ConstructionTargets.SurfaceClassification.separatingCurvesCoboundAnnulus`;
this lemma uses that same mathematical interface specialized to the frozen
problem definitions.

## Assembly

The main theorem first applies `apm_t01J01_nullHomologySeparates` to each
curve, then passes the resulting two separation facts together with
disjointness and essentiality to
`apm_t01J01_separatingCurvesCoboundAnnulus`.  Its proof contains no `sorry`.

## Dependency layers

* **Layer 1 (parallel):** `apm_t01J01_nullHomologySeparates` and
  `apm_t01J01_separatingCurvesCoboundAnnulus`.
* **Layer 2 (already compiled):** the main-theorem assembly after both library
  lemmas are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t01J01/Blueprint.lean
```

The final output was:

```text
holes/labs/blueprints/t01J01/Blueprint.lean:54:8: warning: declaration uses `sorry`
holes/labs/blueprints/t01J01/Blueprint.lean:68:8: warning: declaration uses `sorry`
'apm_t01j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings are exactly the two LIBRARY lemmas.  The main theorem has no
direct `sorry`; `sorryAx` reaches it only through those lemmas.

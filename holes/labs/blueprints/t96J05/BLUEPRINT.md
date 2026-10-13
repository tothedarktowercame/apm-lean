# Blueprint for t96J05

## Triage

Verdict: **true and faithful**.

The original problem allows the intersection to have the same dimension as
`X`.  The current statement reflects this by existentially choosing `k ≤ m`;
it does not force dimension `m - 1`.  This matters for a connected submanifold
lying on one sphere: its only inhabited radial level is all of `X`, and hence
has dimension `m`.  The topology ledger's compiled unit-circle refutation
applied to the older codimension-one encoding, not to this registered theorem.

Degenerate checks:

* `m = 0` is excluded by `hm`.
* Nonemptiness plus positive manifold dimension prevents `X` from being only
  the ambient origin (locally a positive-dimensional Euclidean open set has
  more than one point).
* If the squared radius is constant, its value is therefore positive and the
  intersection with that sphere is exactly `X`.
* If it is nonconstant, connectedness makes its image a nondegenerate interval.
  The interior consists of positive attained values, and Sard supplies a
  regular one.

No statement repair is needed.

## Definitions

`Blueprint.lean` repeats the three definitions used in `Main.lean`: the
Euclidean model, the literal norm-level subtype, and the predicate saying that
this subtype has some smooth Euclidean manifold structure of dimension at most
`m` whose map into the ambient Euclidean space is smooth.

## Lemmas

### `apm_t96j05_constant_radius_level`

**Statement.** If every point of an embedded smooth `m`-manifold `X` has the
same positive norm `r`, then the literal radial level at `r` is nonempty and is
an embedded smooth radial level (take dimension `m`).

**Why true.** The predicate defining the level is true for every `x : X`, so
the level subtype is equivalent to `X`. Transport the supplied charted-space
and manifold structures across this equivalence. The ambient inclusion is the
original inclusion after the equivalence, hence is smooth.

**Expected size.** 40–80 lines.

**Dependencies.** Definitions only. It is independent of the other two
lemmas.

**Truth check.** For the unit circle, `r = 1` and the level is the whole
circle; choosing `k = m = 1` is valid. For a singleton at the origin the
positivity hypothesis cannot hold, so this lemma does not conceal the excluded
zero-radius case.

### `apm_t96j05_exists_regular_radius` — LIBRARY

**Statement.** On a nonempty connected positive-dimensional smooth manifold,
a smooth squared-radius map which is not constant at a positive radius has an
attained positive norm level `r` on which its manifold derivative is
surjective.

**Why true.** Positive dimension makes the domain nontrivial, so the negated
constant-radius alternative implies that squared radius is nonconstant. Its
continuous image is therefore a nondegenerate interval in `[0,∞)`. Choose a
nonempty open interval inside that image; it lies in `(0,∞)`. Manifold Sard
says the critical values have measure zero, whereas this interval has positive
measure. Pick a regular value `c` in it and put `r = sqrt c`. Membership in the
image gives an inhabitant, positivity gives `r > 0`, and `r² = c` converts the
regular-value assertion to the displayed derivative condition.

**Expected size.** 300+ lines. This is intentionally one **LIBRARY** lemma:
the missing boundary is the general finite-dimensional manifold Sard theorem,
not a collection of honest 30-line consumer lemmas. The closest existing
infrastructure is the sorry-free `ConstructionTargets/Sard*` development; the
audit `/home/joe/notes/closer/audits/t01A08.edn` names the remaining shared
targets `ConstructionTargets.SardGeneralModel.modelRange_geometry` and
`ConstructionTargets.SardConvexDomain.criticalImageNull`. This is the same
shared arbitrary-model Sard foundation used by t01A08 and t01J04.

**Dependencies.** Definitions and Mathlib's connected-image/measure facts;
independent of the constant-level and regular-fiber assembly lemmas.

**Truth check.** For `X = ℝ` embedded as a line, squared radius has regular
positive levels at every `r > 0`. For a circle centered away from the origin,
the two extremal radii are critical but every intermediate radius is attained
and regular. For the unit circle centered at the origin the nonconstant
hypothesis fails, correctly routing it to the preceding lemma.

### `apm_t96j05_regular_radius_level`

**Statement.** A positive, inhabited radial level whose squared-radius
derivative is surjective at every point has the required embedded smooth
structure.

**Why true.** Apply
`ConstructionTargets.ManifoldRegularFiberGlobalAtlas` to the squared-radius
fiber. Transport its fixed model to
`EuclideanSpace ℝ (Fin (m - 1))` using
`ContinuousLinearEquiv.ofFinrankEq`, then transport the atlas across
`ConstructionTargets.RadialSquaredFiber.norm_sq_eq_sq_iff hr`. Compose the
fiber inclusion into `X` with the supplied smooth inclusion of `X` into the
ambient Euclidean space. Choose `k = m - 1`; `Nat.sub_le` proves `k ≤ m`.

**Expected size.** 80–140 lines.

**Dependencies.** Definitions and the imported, sorry-free regular-fiber
modules only; independent of the other two lemmas.

**Truth check.** On a line through the origin and `r > 0`, the level consists
of two points, matching dimension `m - 1 = 0`. The positivity assumption is
essential for identifying equality of squares with equality of norms.

## Assembly and dependency layers

The main theorem opens the embedded-manifold witness and splits on whether
there is a positive radius constant on all of `X`. The constant branch invokes
the first lemma. In the other branch, smoothness of squared norm follows from
`contDiff_norm_sq`; the Sard lemma chooses `r`, and the regular-fiber lemma
constructs the embedded level.

* **Layer 1 (all parallel):**
  `apm_t96j05_constant_radius_level`,
  `apm_t96j05_exists_regular_radius` (LIBRARY),
  `apm_t96j05_regular_radius_level`.
* **Layer 2 (already compiled, no seat):** `apm_t96j05` assembly after all
  three Layer 1 results.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96J05/Blueprint.lean
```

The output of `#print axioms apm_t96j05` is:

```text
'apm_t96j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three warnings are exactly the three top-level blueprint lemmas. The main
theorem contains no `sorry`.

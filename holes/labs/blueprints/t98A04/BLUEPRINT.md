# Blueprint for t98A04

## Triage and repair

Verdict: **unfaithful as registered; repaired**.

The point-set sphere, fibers, corrected section type `S² → S³`, and no-section
conclusion in `Main.lean` are faithful.  The defect is the definition of
`apm_t98a04_IsSubmersion`: it existentially chooses the source
`ChartedSpace`.  Thus it does not say that the displayed Hopf map is a
submersion for the ordinary smooth structure on the sphere fixed in the
problem.  This is exactly the defect recorded by
`holes/labs/statement-registry/triage-3.md`.

`RevisedMain.lean` makes the smallest repair recommended there.  It replaces
the ad-hoc subtype by Mathlib's
`Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1`, supplies the elementary
real-finrank fact `4 = 3 + 1`, and consequently uses Mathlib's fixed
`EuclideanSpace.instChartedSpaceSphere`.  The source atlas is removed from the
existential submersion predicate.  The target atlas remains existential,
because Mathlib has no installed smooth atlas for this projectivization.  No
mathematical hypothesis or conclusion from `problem.md` was dropped.

There is no short logical counterexample to compile in `Refute.lean`: the old
claim is under-specified rather than contradicted by a concrete input.  Its
witness may select an arbitrary source atlas, so even proving it would not
answer the sentence “Show that π is a submersion” for the standard `S³`.

Degenerate checks:

* The repaired sphere is nonempty (for example `(1,0)`) and excludes zero;
  `apm_t98a04_sphere_ne_zero` is compiled.
* The base point `[1:0]` is represented by a nonzero vector.
* Scalar normalization has no zero-norm branch because every source vector
  has norm one.
* A hypothetical section cannot evade the obstruction by an empty domain:
  `CP¹` contains `[1:0]`.

The topology worklists contain no dedicated `t98A04` producer.  Their nearest
Hopf entries concern the different invariant-surface problem `t95J06` and do
not prove any contract below.  The solve loop's recorded exact residual agrees
that the missing items are the smooth atlas/submersion, normalized fibers, and
global no-section obstruction.

## Reused compiled facts

`apm_t98a04_sphere_ne_zero` proves that a unit-sphere point is nonzero.
`apm_t98a04_continuous_hopf` factors the map through the coinduced quotient
topology and is sorry-free.  The blueprint imports the sorry-free
`ConstructionTargets.ComplexProjectiveChartTargets`, whose affine-coordinate
definitions and proved inverse/source facts are the closest existing start for
the target atlas.

## Remaining lemmas

### `apm_t98a04_submersion_bridge` — LIBRARY

**Statement.** The Hopf map from Mathlib's standard metric sphere admits the
usual smooth `CP¹` target atlas, is smooth, and has surjective manifold
derivative everywhere.

**Why true.** Build the two affine projective charts `z₂/z₁` and `z₁/z₂`
from `ConstructionTargets.ComplexProjectiveChartTargets`.  In either chart the
differential is the nonzero complex-linear functional
`(z₁ dz₂ - z₂ dz₁)/z₁²` (or its symmetric version).  Its kernel in the ambient
space is `ℂ z`; intersecting with the tangent space to the unit sphere leaves
`iℝ z`, so the real rank is two.  Mathlib supplies the standard source sphere
atlas and manifold instance; what is missing is a packaged smooth
projectivization atlas compatible with the existing quotient topology.

**Expected size.** 300+ lines; intentionally one LIBRARY target rather than
fake small lemmas.

**Dependencies.** Definitions and the imported affine projective chart
module only.

**Truth check.** At `(1,0)` the affine formula is locally `z₂/z₁`, and tangent
variations in the two real `z₂` directions map isomorphically to `ℂ`.  The
same check at `(0,1)` uses the other chart.  Every sphere point lies in one of
these cases.

### `apm_t98a04_fiber_eq_circleOrbit`

**Statement.** If `z` lies over `p`, the entire fiber over `p` is exactly the
unit-complex-scalar orbit of `z`.

**Why true.** Use `Projectivization.mk_eq_mk_iff'` to obtain a nonzero complex
scalar relating two representatives.  Equality of their unit norms forces
the scalar norm to be one, hence it is an element of `Circle`.  Conversely,
projectivization is unchanged by a nonzero unit scalar.

**Expected size.** 60–110 lines.

**Dependencies.** Definitions only.

**Truth check.** Scalar `1` gives the base point, scalar `-1` gives its
antipode, and scalar `0` is excluded by `Circle`.  Norm one rules out all
radial scalings of modulus other than one.

### `apm_t98a04_fiber_p10`

**Statement.** The fiber over `[1:0]` consists exactly of unit-sphere vectors
whose second coordinate is zero.

**Why true.** Apply `Projectivization.mk_eq_mk_iff'`.  Proportionality to
`(1,0)` immediately makes coordinate `1` zero.  Conversely, a unit vector
with second coordinate zero has nonzero first coordinate and is projectively
equal to `(1,0)`.

**Expected size.** 35–70 lines.

**Dependencies.** Definitions only.

**Truth check.** `(1,0)` and `(-1,0)` lie in both sets.  `(0,1)` lies in
neither.  The impossible candidate `(0,0)` is excluded by the sphere.

### `apm_t98a04_fiber_homeomorph_circle`

**Statement.** Every fiber is homeomorphic to `Circle`.

**Why true.** Normalize `Projectivization.rep p` to obtain a chosen unit
representative `z`.  Map `u : Circle` to `u • z`; its inverse extracts the
unique scalar, for example from a nonzero coordinate of `z`.  Prove the two
maps continuous locally (split on which coordinate of `z` is nonzero), then
package a `Homeomorph`.  The preceding orbit lemma is not made a dependency:
the coordinate proof directly establishes the image, allowing both seats to
work in parallel without accepting an unfinished theorem.

**Expected size.** 100–150 lines.

**Dependencies.** Definitions only.

**Truth check.** For `p=[1:0]`, the maps reduce to
`u ↦ (u,0)` and first-coordinate projection.  The same construction for
`[0:1]` uses the second coordinate; normalization prevents a zero denominator.

### `apm_t98a04_no_section_bridge` — LIBRARY

**Statement.** The concrete Hopf map has no continuous right inverse.

**Why true.** A section would make the identity on second integral singular
homology of `CP¹ ≅ S²` factor through that of `S³`.  The middle group is zero
and the first is `ℤ`, contradiction.  An equivalent implementation can use
the long exact homotopy sequence.  Mathlib does not package the necessary
concrete identifications and induced-map bridge for this quotient model, so
this is kept as one honest library-scale target.

**Expected size.** 300+ lines.

**Dependencies.** Definitions and the compiled continuity lemma.

**Truth check.** At the point-set level every projective point has a unit
representative, but choosing it continuously would choose a phase globally.
On the coordinate overlap the transition function has winding number one,
which is precisely the obstruction.  The homology calculation agrees:
`H₂(S³)=0` and `H₂(S²)=ℤ`.

## Dependency layers

* **Layer 1 (parallel):** all five remaining lemmas.  Each has a self-contained
  statement over the shared definitions; none assumes another unfinished
  lemma.
* **Layer 2 (sorry-free assembly):** `apm_t98a04`, after all Layer 1 results
  are supplied.

## Compilation and axioms

Both Lean files were compiled with the required 12G systemd scope.  The final
output of `#print axioms apm_t98a04` is:

```text
'apm_t98a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The five warnings identifying `sorry` are exactly the five top-level Layer 1
lemmas.  The main theorem and its assembly contain no direct `sorry`.

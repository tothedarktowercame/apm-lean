# t95A04 blueprint: the Veronese embedding of RP²

## Triage

Verdict: **true and faithful**.  The registered theorem says exactly that the
printed even quadratic map on `Sphere 2` descends to the fixed real-projective
quotient, is smooth, is a topological embedding, and is an immersion in
Mathlib's local-normal-form sense.  This matches the sentence in `problem.md`.

I tried the relevant degenerate cases before retaining the statement:

* The zero vector cannot occur because the source is the unit sphere.
* Points with two zero coordinates are handled by the square coordinate at the
  remaining nonzero coordinate.  More generally, the already proved theorem
  `RealProjectiveVeroneseFibers.veroneseSphereMap_eq_iff` explicitly selects a
  nonzero coordinate and therefore covers every pattern of zero coordinates.
* The map is unchanged at the antipode, since every printed coordinate is a
  product of two coordinates.  Hence the formula is well-defined on RP².
* At a coordinate-axis point, the derivative still has rank two on the sphere
  tangent plane: for example at `(1,0,0)`, tangent vectors `(0,a,b)` map to the
  two cross-term directions `(a,b)`.

The topology worklist's former atlas/descent blockers have been discharged in
the sorry-free modules `RealProjectiveSmoothTarget`,
`RealProjectiveEvenQuadraticDescent`, and `RealProjectiveVeroneseFibers`.
There was no t95A04 solve-loop cache or t95A04 solve-loop ledger row to reuse.

## Reused results (already proved)

The blueprint imports the following sorry-free construction targets:

* `rpSmoothAtlas` and `sphereProjectionEvenMapSmoothDescent` provide the atlas
  and smooth quotient descent.
* `veroneseDescended_sphereProjection` identifies the descended map with the
  six printed coordinates.
* `veroneseDescended_contMDiff` proves smoothness.
* `veroneseDescended_injective` proves injectivity, including all zero-coordinate
  cases.

The compactness theorem and embedding adapter in `Blueprint.lean` are also
proved, not assigned as holes.  Compactness is the continuous image of compact
`Sphere 2`; `Continuous.isClosedEmbedding` then turns continuous injectivity
from this compact space into an embedding in the Hausdorff Euclidean target.

## Assigned lemmas

### 1. `t95A04_veroneseDescended_mfderiv_injective`

**Statement in words.**  At every point of RP², the manifold derivative of the
descended Veronese map is injective.

**Why true.**  Lift the point to `p : Sphere 2` and use the banked local
diffeomorphism for `sphereProjection`.  For an ambient vector `v`, the
derivative of `p ↦ ppᵀ` is `pvᵀ + vpᵀ`.  If it vanishes, multiplying by `p`
gives `v + (v · p)p = 0` because `‖p‖ = 1`; substituting this back (or taking its
inner product with `p`) gives `v = 0`.  Restriction to the sphere tangent space
is therefore injective, and composition with the inverse derivative of the
local diffeomorphism transports injectivity to RP².  Likely APIs are
`rpSmoothAtlas.quotient_localDiffeomorph`, the chain rule for `mfderiv`, and
coordinatewise `fderiv` rules for products and `PiLp.toLp`.

**Estimate.** 120–200 lines.

**Dependencies.** None of the other assigned lemmas; it uses only the
definitions and imported construction targets.

**Truth check.**  Hand-computed the full Jacobian and checked the axis point
`p=(1,0,0)` separately.  The kernel argument uses only `p ≠ 0`, which is forced
by sphere membership.

### 2. `t95A04_isImmersion_of_injective_mfderiv` — LIBRARY

**Statement in words.**  If the manifold derivative of this descended map is
injective everywhere, then the map satisfies Mathlib's `Manifold.IsImmersion`
local coordinate normal form.

**Why true.**  This is the finite-dimensional immersion/constant-rank theorem:
an injective derivative can be completed by a four-dimensional complement,
and the inverse function theorem applied to the map consisting of `f` plus
complement coordinates gives charts in which `f(u)=(u,0)`.  The hypothesis is
the conclusion of lemma 1, passed explicitly so this lemma can be developed in
parallel; it is not baked into a definition and does not assume its own result.

**Estimate.** 300–800 lines (LIBRARY/program-sized).

**Dependencies.** It accepts lemma 1's conclusion as a hypothesis, so its proof
development is layer-1 parallel with lemma 1.

**Truth check.**  This is the standard finite-dimensional constant-rank
theorem.  It is valid here because both model spaces are finite-dimensional
Euclidean spaces (dimensions 2 and 6) and the map is already smooth.

**Why this remains LIBRARY.**  I searched every sorry-free
`ConstructionTargets/*.lean` module for projective, Veronese, embedding, and
immersion results.  The closest files are the three reused projective modules
above; none supplies the derivative-to-local-normal-form bridge.  Mathlib's
`Geometry/Manifold/Immersion.lean` explicitly lists as a TODO the equivalence
with injectivity of `mfderiv` for finite-dimensional manifolds (its introductory
comment and TODO near lines 17 and 82).  Thus this is the actual missing
theorem named by the topology worklist, not an artificial decomposition.

## Dependency layers

* **Layer 0 (done):** atlas, smooth descent, exact fibers/injectivity,
  compactness, and the compact-to-Hausdorff embedding adapter.
* **Layer 1 (parallel):** lemma 1; lemma 2 developed with its explicit
  `hderiv` hypothesis.
* **Layer 2 (assembly, done):** instantiate lemma 2 with lemma 1 and combine it
  with the imported smoothness/formula results and proved embedding adapter.

## Compilation and axioms gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t95A04/Blueprint.lean
```

Result: success, with warnings only on the two assigned `sorry` bodies.

`#print axioms apm_t95a04` output:

```text
'apm_t95a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The main theorem has no `sorry`; `sorryAx` enters only through the two assigned
top-level lemmas.

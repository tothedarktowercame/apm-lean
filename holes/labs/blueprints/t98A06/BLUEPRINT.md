# Blueprint for t98A06

## Triage

Verdict: **true and faithful**.  No statement repair is needed.

The first conjunct is the literal smooth-manifold formulation of part (a):
`SmoothVectorField` says that the section into the actual tangent bundle is
smooth, and the displayed `mfderiv` equation is `df_x(w(x)) = v(f(x))`.
The second conjunct specializes to a compact boundaryless manifold (the
self-model `𝓡 n` has no boundary) and uses the constructed induced atlases on
the literal fibers over `1` and `minusOne`.  This is exactly the diffeomorphism
asserted in part (b).

Degenerate checks:

* If `X` is empty, both fibers in part (b) are empty and are diffeomorphic.
* If `n = 0` in part (b) and `X` is nonempty, a derivative from a zero
  tangent space to the one-dimensional circle tangent space cannot be
  surjective, so the hypotheses do not create a counterexample.
* A constant map from nonempty `X` to `Circle` likewise cannot satisfy
  `hsub`.
* In part (a), zero-dimensional source/target cases reduce to the unique zero
  vector fields, and an empty source makes the conclusion vacuous.

The solve-loop ledger records no counterexample.  Its two reviewed attempts
both stopped at the same genuine representation boundary: Mathlib has
pointwise finite-dimensional right inverses but no theorem producing a smooth
family of them in varying tangent fibers.  The audit also identifies smooth
dependence on initial conditions for complete flows as the major missing
foundation in part (b).

## Definitions

`HasLocalSmoothLift f v` records the exact local datum needed for convex
partition-of-unity gluing: at every `x₀`, on some neighborhood, there is a
smooth tangent section mapped by `mfderiv f` to `v ∘ f`.

`HasSmoothLift f v` records the global conclusion of part (a).  Neither
predicate assumes its intended conclusion indirectly: the local predicate
contains only neighborhoodwise data, while the global predicate is used as a
named interface between the independently assigned foundations.

## Remaining lemmas

### `t98A06_local_smooth_submersion_lift` — LIBRARY

**Statement in words.** Every smooth submersion between the manifolds in the
registered statement admits a neighborhoodwise smooth lift of every smooth
target vector field.

**Why true.** At a fixed `x₀`, choose a complement of
`ker (mfderiv f x₀)`.  In compatible tangent-bundle charts, restrict the
varying derivative to that fixed complement.  It is invertible at `x₀`, hence
remains invertible after shrinking.  Smoothness of matrix inversion gives a
smooth local right inverse; applying it to `v (f x)` and transporting back
through the tangent charts gives the required local section.

The closest existing API consists of pointwise
`ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional` and
fixed-space smooth inverse machinery.  The missing result is the assembly in
varying tangent charts.  This is precisely the STOP named in the topology
ledger; no sorry-free `ConstructionTargets` module currently supplies it.

**Expected size.** 250–500 lines.  This is intentionally one LIBRARY theorem,
not fake small lemmas around the missing chart-trivialization program.

**Dependencies.** Definitions only.

**Truth check.** In Euclidean charts this is the familiar fact that a smooth
family of surjective matrices has a smooth local family of right inverses.  At
`n = m = 0` the zero map is its own right inverse, and for `m > n` the
surjectivity hypothesis is impossible.

### `t98A06_global_vectorField_lift`

**Statement in words.** Assuming the preceding neighborhoodwise theorem,
local derivative lifts glue to one global smooth lift.

**Why true.** For each `x`, take the affine fiber

`{u : T_x X | mfderiv f x u = v(f x)}`.

It is convex because `mfderiv f x` is linear.  Feed the local sections to
`exists_contMDiffSection_forall_mem_convex_of_local` from
`Mathlib.Geometry.Manifold.PartitionOfUnity`.  The resulting global smooth
section lies in every affine fiber, which is exactly `HasSmoothLift f v`.
The topology loop had a compiled fixture validating this downstream gluing;
the fixture itself was temporary and is no longer present, so the blueprint
keeps this adapter as the bounded seat rather than claiming a recovered proof.

**Expected size.** 60–120 lines.

**Dependencies.** Takes the conclusion of
`t98A06_local_smooth_submersion_lift` as a hypothesis, so it can be assigned in
parallel with that theorem.

**Truth check.** Each affine fiber is nonempty locally, and convexity follows
by applying linearity to `a u + b w` with `a+b=1`.  In the empty-source case,
the resulting global section and its equation are vacuous.

### `t98A06_compact_circle_fibers_diffeomorphic` — LIBRARY

**Statement in words.** Assuming the global lift theorem, the two indicated
fibers of any compact submersion to the circle are diffeomorphic with their
already constructed regular-fiber smooth structures.

**Why true.** Use the unit angular vector field on `Circle` and `hlift` to
obtain a smooth vector field `w` on `X` related to it by `f`.  A smooth vector
field on compact boundaryless `X` has a complete flow, smooth jointly in time
and initial condition.  Uniqueness of integral curves shows that applying `f`
to this flow is circle rotation.  Time `π` therefore maps the fiber over `1`
to the fiber over `minusOne`; time `-π` is its smooth inverse.  Restrict these
maps and use the regular-fiber atlas API imported from
`ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas` to bundle the
result as the displayed `Diffeomorph`.

Mathlib provides local existence/uniqueness and
`exists_isMIntegralCurve_of_isMIntegralCurveOn`, but the audit records the
remaining compact uniform-time and smooth-in-initial-condition construction as
300–3000 lines.  No sorry-free construction target supplies that package, so
this is one honest LIBRARY boundary rather than several circular flow lemmas.

**Expected size.** Library program: roughly 1200–3000 lines for the missing
smooth-flow foundation, followed by a 180–350 line fiber restriction adapter.

**Dependencies.** Takes the conclusion of
`t98A06_global_vectorField_lift` as a hypothesis, allowing this program to run
in parallel with both part-(a) seats.

**Truth check.** Rotation by `π` sends exactly `1` to `-1`, and the group law
makes time `-π` the inverse.  For empty `X`, both restricted maps are the
unique maps between empty fibers.  Compactness is used only for completeness,
not for an unjustified surjectivity assertion.

## Assembly

The main theorem first applies `t98A06_global_vectorField_lift` to the local
LIBRARY theorem.  It pairs that result with
`t98A06_compact_circle_fibers_diffeomorphic` applied to the same global lift.
The main theorem contains no `sorry` and its type is copied unchanged from
`problems/t98A06/lean/Main.lean`.

## Dependency layers

* **Layer 1 (parallel):**
  `t98A06_local_smooth_submersion_lift`,
  `t98A06_global_vectorField_lift` (with the local conclusion as a hypothesis),
  and `t98A06_compact_circle_fibers_diffeomorphic` (with the global conclusion
  as a hypothesis).
* **Layer 2 (sorry-free assembly):** instantiate the two hypotheses and prove
  `apm_t98a06`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t98A06/Blueprint.lean
```

The output of `#print axioms apm_t98a06` is:

```text
'apm_t98a06' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The three warnings are exactly the three top-level lemmas above.  The main
theorem and all definitions contain no direct `sorry`.

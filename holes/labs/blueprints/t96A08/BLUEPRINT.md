# Blueprint for t96A08

## Triage and repair

Verdict: **unfaithful (vacuous encoding), repaired**.

The registry grader's objection is correct.  The source quantifies over
piecewise-smooth paths in the textbook sense.  The old definition required a
continuous path to be smooth merely away from a finite set.  That permits, in
a real chart, oscillatory curves such as

`g(t) = t * sin (1 / t^2)` for `t > 0`, with `g(0) = 0`,

continued smoothly away from zero.  The derivative has a non-integrable
oscillatory term of order `1/t^2`.  For a nonzero constant coordinate one-form,
the integrand in the old `LineIntegral` is therefore not interval-integrable.
Lean's Bochner integral is defined to be zero for a non-integrable function,
so the old `hindependent` does not express the source's path independence and
can force the theorem for the wrong, vacuous reason.

`Refute.lean` is omitted: compiling the absolute non-integrability of that
oscillatory derivative would itself be a substantial real-analysis exercise,
and the registry already records the counterexample.  The semantic failure is
in the old definition, not a short finite countermodel to the final
proposition.

The repair in `RevisedMain.lean` changes only
`apm_t96a08_IsPiecewiseSmoothPath`.  A path now has a finite strictly ordered
subdivision from `0` to `1` and is `ContMDiffOn` every closed subinterval.
This is precisely the grader's recommended repair and the usual meaning of
piecewise smooth.  Smoothness up to both endpoints on each compact piece makes
the pulled-back smooth one-form integrable; the finitely many endpoint values
of the global `mfderiv` do not affect the interval integral.  The already
accepted repairs `f : M → ℝ` and `hreachable` are unchanged.

Degenerate checks:

* A subdivision with `n = 0` would require its sole cut to equal both `0` and
  `1`, so it cannot spuriously witness a path.
* Constant paths are admitted using the two cuts `0,1`, and have integral
  zero.
* At a cut, the two closed pieces impose one-sided smoothness from both sides.
  A jump is independently excluded by global continuity.
* The grader's oscillatory curve fails `ContMDiffOn` the first closed piece at
  zero, so it does not survive the repair.
* Empty and zero-dimensional manifolds cause no false case: `base : M` makes
  `M` nonempty, and in dimension zero the asserted derivative identity is the
  equality of the unique zero cotangent maps.

No t96A08 entry was present in the topology-contract worklists or the audit
directory, and there was no cached solve-loop file or per-problem solve-loop
record beyond the source file's existing account of the same obstruction.

## Definitions

`apm_t96a08_IsPiecewiseSmoothPath I gamma` is the repaired finite closed-piece
predicate above.  `apm_t96a08_LineIntegral I omega gamma` retains the original
concrete interval integral of the one-form applied to `mfderiv gamma`.

## Split library lemmas

### `apm_t96A08_piecewisePath_concat_additive`

Construct the two-speed concatenation and combine the two finite cut lists;
then prove integral additivity by affine changes of variables. Independent of
all other new lemmas. Expected size: **90--140 lines**.

Useful Mathlib API: `Continuous.piecewise`, `ContMDiffOn.comp`,
`intervalIntegral.integral_add_adjacent_intervals`,
`intervalIntegral.integral_comp_mul_deriv`, `integral_congr_ae`, and `Fin`
lemmas for joining cut lists. The integrand value at the single join is
irrelevant almost everywhere.

Degenerate checks: constant paths work; continuity at the join follows from
the endpoint equality; old endpoints remain in closed pieces; both affine
maps are increasing, so there is no orientation sign, and their speed factors
cancel the half-interval substitutions.

### `apm_t96A08_chart_radial_primitive`

Shrink a chart at `x` to the inverse image of a convex ball and integrate on
the chart-linear segment from `x` to `z`. Prove the resulting local function
smooth and compute its derivative at `x`. Independent of concatenation and of
`f`. Expected size: **120--150 lines**. If chart bookkeeping pushes it over
that bound, split construction of the convex chart neighbourhood from the
parameter-integral calculation, passing the coordinate formula explicitly.

Useful Mathlib API: `extChartAt`, chart source/target openness,
`Metric.isOpen_ball`, convexity of norm balls, `ContMDiff.cl_mfderiv`,
`hasFDerivAt_integral_of_dominated_of_fderiv_le` (or the interval-integral
variant), `writtenInExtChartAt`, and `mfld_simps`. Do not import `SphereCap*`
or `LinearGraphMeasure`.

Degenerate checks: `z = x` gives the constant segment and zero integral;
closed-piece smoothness includes `t = 0,1`; in dimension zero both derivative
maps are uniquely zero. Choose a positive-radius ball whose closure stays in
the chart target, so boundary points do not escape the chart.

### `apm_t96A08_potential_of_local_primitives`

For fixed `x`, append each radial path to a chosen path from `base` to `x`.
Additivity and `hf` yield `f z - f x = g z - g x`; use this local equality to
transfer smoothness and derivative, then globalize. Both substantive results
are explicit hypotheses, so this seat can be proved in parallel with them.
Expected size: **45--80 lines**.

Useful Mathlib API: `ContMDiffOn.congr`, `contMDiff_iff_contMDiffAt`,
`ContMDiffAt.congr_of_eventuallyEq`, `mfderiv_congr_of_eventuallyEq`, and the
derivative rules for adding a constant.

Degenerate checks: `hreachable` handles `base`; the neighbourhood is nonempty
because it contains `x`; the local additive constant has derivative zero.
This is not vacuous: it requires both structural properties and the full path
specification `hf`.

### `apm_t96A08_piecewise_lineIntegral_fundamental` (assembly)

Sorry-free assembly of the three lemmas above; its registered statement is
unchanged.

## Assembly

The main theorem uses classical choice to select one reachable path to each
point and defines `f` to be its integral.  `hindependent` proves the full `hf`
specification.  The assembled lemma supplies smoothness and `mfderiv f = omega`.
This assembly is sorry-free.

## Dependency layers

* **Layer 1 (parallel):** concatenation/additivity and chart radial primitive.
* **Layer 2 (also independently provable):** abstract potential/locality glue.
* **Layer 3:** sorry-free fundamental-lemma assembly.
* **Layer 4 (already proved):** choice, well-definedness, and final assembly.

## Compilation and axioms

Both files compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96A08/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96A08/Blueprint.lean
```

The final output of `#print axioms apm_t96a08` was:

```text
'apm_t96a08' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The `sorryAx` dependencies enter only through the three independent leaf
lemmas. The fundamental lemma and main theorem have no direct `sorry`.

**claude-14 review fix (2026-10-13).** `apm_t96A08_piecewisePath_concat_additive` now assumes `homega_smooth`.
Without any regularity of `omega`, the integrand along `gamma` can be non-integrable (interval integral `0`
by convention) while `delta`'s is not, and the concatenation's integral is then `0 ≠ 0 + ∫delta`: the
statement was not true for arbitrary `omega`. With `omega` continuous on the tangent bundle, each closed
smooth piece gives a bounded, piecewise-continuous integrand, so the affine-reparameterised integrals add.

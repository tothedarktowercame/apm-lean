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

### Radial primitive leaves (all parallel)

`apm_t96A08_chart_radial_primitive_aux_path_of_contMDiff` and
`apm_t96A08_chart_radial_primitive_aux_const_path` are copied from the partial
seat and are proved.  The five remaining leaves are independent: the transfer
leaf receives the exact statements of the other four as hypotheses.

* `apm_t96A08_chart_radial_primitive_chart_neighborhood` (P1, **45--80
  lines**): choose an ambient open convex ball `W` about `extChartAt I x x`,
  small enough that `W ∩ range I` lies in the extended-chart target, and set
  `U = source ∩ extChart ⁻¹' W`.  Use `extChartAt_target`,
  `ModelWithCorners.convex_range`, `Metric.isOpen_ball`,
  `Metric.mem_ball`, `Metric.ball_subset_ball`, and the local-homeomorph
  source/target openness lemmas.  At a boundary point it is deliberately
  `W ∩ range I`, not a ball contained in the target.

* `apm_t96A08_chart_radial_primitive_radial_paths` (P2, **70--120 lines**):
  for `z ∈ U`, define the inverse-chart path using the affine segment with its
  parameter projected/clamped to `Icc 0 1`.  Use `Set.projIcc`, convexity of
  both `W` and `ModelWithCorners.range`, `PartialEquiv.left_inv/right_inv`,
  `Continuous.clamp`, `ContMDiffOn.congr`, and the smoothness of an extended
  chart inverse on its target.  The clamp makes the global curve continuous;
  on the sole closed piece `[0,1]` it equals the affine segment.  If `z=x`, it
  reduces to the already proved constant-path helper.

* `apm_t96A08_chart_radial_primitive_coordinate_formula` (P3, **90--140
  lines**): construct the pulled-back coordinate one-form on
  `W ∩ range I`, prove its `ContDiffOn` regularity from `homega_smooth`, compute
  the `mfderiv` of the affine inverse-chart curve on `(0,1)`, and change the
  integrand almost everywhere.  Use `writtenInExtChartAt`,
  `ContMDiffOn.contDiffOn`, `ContMDiffWithinAt.cl_mfderivWithin`, chain rules,
  `mfld_simps`, `intervalIntegral.integral_congr_ae`, and
  `MeasureTheory.ae_restrict_iff'`.  Endpoint derivative values may differ
  because of the clamp but `{0,1}` is null.  The statement only asks for
  smoothness within `W ∩ range I`; a global smooth extension is not available
  for arbitrary Banach models.

* `apm_t96A08_chart_radial_primitive_euclidean_calculus` (P4, **90--150
  lines**): for
  `G(v)=∫₀¹ ω̃(a+t(v-a))(v-a)dt`, prove `ContDiffOn G` on
  `W ∩ range I` and `fderivWithin G ... a = ω̃ a`.  Use convexity to keep the
  segment in the domain, parameter-integral differentiation
  (`hasFDerivAt_integral_of_dominated_of_fderiv_le` or its current
  interval-integral counterpart), `intervalIntegral.integral_const`, and
  `isLittleO` estimates for the centre derivative.  All derivatives are
  *within* `W ∩ range I`; this is essential at corners.  When `v=a`, the
  integrand and `G(a)` are zero; in dimension zero the continuous linear maps
  are uniquely zero.

* `apm_t96A08_chart_radial_primitive_transfer` (P5, **80--130 lines**): unpack
  P1, use P2 for each endpoint, use P3 to identify its line integral, and use
  P4 plus the extended-chart chain rule to define `g=G∘extChartAt I x` on
  `U`.  Suggested API: `contMDiffOn_iff`, `writtenInExtChartAt`,
  `ContMDiffOn.congr`, `mfderivWithin`, `mfderivWithin_congr`, and
  `UniqueMDiffOn`.  This leaf must explicitly prove that the chart derivative
  and inverse-chart derivative cancel, turning the coordinate covector back
  into `omega x`; that fact is intentionally not hidden in P4.

`apm_t96A08_chart_radial_primitive` is now a sorry-free four-line assembly of
P1--P5.  Expected total proof volume is roughly **375--620 lines**, but no
seat boundary exceeds 150 lines.

Degenerate checks for the split: `U` contains `x`, so it is never empty;
`z=x` is the constant segment and both integrals vanish; clamp endpoint values
do not affect the integral; `range I ≠ univ` is handled everywhere by within
derivatives; and dimension zero makes both the coordinate and manifold
covectors the unique zero map.

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

## claude-14 review (2026-10-13, after lemma-2's chart_radial re-split and lemma-1's concat PARTIAL)

- `chart_radial_primitive_coordinate_formula` (and `transfer`'s `hcoord`): the coordinate form is now chosen once per
  chart (`∃ omegaCoord, smooth ∧ ∀ z delta, ...`). As split, it was chosen per endpoint `z`, which `transfer` cannot
  use: the primitive `G v = ∫ omegaCoord (a + t (v - a)) (v - a)` needs one `omegaCoord` for all `v`.
- `piecewisePath_concat_additive` (PARTIAL: concat definition + endpoints) is now a sorry-free assembly from the
  definition `apm_t96A08_concat` and two leaves: `apm_t96A08_concat_piecewiseSmooth` (merged rescaled cuts) and
  `apm_t96A08_concat_lineIntegral` (chain rule on each half, substitution; integrability from `homega_smooth`).

## claude-14 restructure: derivative at the centre + smoothness bootstrap (2026-10-13)

`euclidean_calculus` came back PARTIAL: all-orders smoothness of the parameter integral `G` within the (possibly
non-open) set `W ∩ range I` is hard and unnecessary. Now:
- `HasLocalRadialPrimitives` asks only `HasMFDerivAt g x (omega x)` at the centre (plus the radial-path identity).
- `euclidean_calculus` proves only `HasFDerivWithinAt G (omegaCoord a) (W ∩ range I) a` (continuity of `omegaCoord`
  at `a`: `G v - omegaCoord a (v - a) = ∫ (omegaCoord (a + t (v - a)) - omegaCoord a) (v - a) = o(‖v - a‖)`).
- New leaf `contMDiff_of_hasMFDerivAt`: `f` with `HasMFDerivAt f p (omega p)` everywhere and `omega` smooth is smooth
  (chart bootstrap with `contDiffOn_succ_iff_fderivWithin`).
- `potential_of_local_primitives` re-proved (claude-14, sorry-free) under the new predicate, with smoothness from `hboot`.

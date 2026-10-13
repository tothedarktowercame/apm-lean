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

## Remaining lemma

### `apm_t96A08_piecewise_lineIntegral_fundamental` (LIBRARY)

**Statement in words.** Let a smooth one-form be given on a smooth manifold.
If every point is reachable from `base` by a repaired piecewise-smooth path,
and a function `f` equals the one-form integral along every such path from
`base`, then `f` is smooth and its manifold derivative is the one-form.

**Why true.** Fix a point and a chart with a smaller convex chart
neighbourhood.  Join `base` to the fixed point and append a chart-linear short
segment to a variable endpoint.  Path independence (already packaged in the
`hf` hypothesis) identifies `f` locally with a constant plus the integral on
that final segment.  In coordinates, smoothness of the tangent-bundle
evaluation map makes the parameter-dependent integrand smooth.  The
parameterized fundamental theorem of calculus shows that this local expression
is smooth and that its derivative at the fixed endpoint is `omega`.  Transfer
the calculation through the chart, then use locality of `ContMDiff`.

This is a genuine missing library theorem, not a useful 30--150 line seat.
It needs the full manifold chart calculation plus a piecewise-path
concatenation/reparameterization and interval-integral splitting API.  The
existing solve attempt independently estimated it beyond a normal lemma seat
and found no compatible Mathlib theorem or sorry-free `ConstructionTargets`
module.  It is therefore stated once rather than split into fake lemmas whose
proofs would duplicate this same calculation.

**Expected size.** 300--600 lines (LIBRARY program).

**Dependencies.** Only the definitions block and Mathlib.  Its `hf` hypothesis
is the independently established path-integral specification, not the lemma's
smoothness/derivative conclusion in disguise.

**Truth check.** The hand proof above is the standard local proof.  On
`M = ℝ` with `omega = dx`, it reduces to the ordinary fundamental theorem of
calculus and gives `f(x) = x - base`.  For `omega = 0`, path independence gives
the constant zero normalized potential and both conclusions follow.  The
oscillatory old-path counterexample is excluded by the repaired closed-piece
hypothesis.

## Assembly

The main theorem uses classical choice to select one reachable path to each
point and defines `f` to be its integral.  `hindependent` proves the full `hf`
specification.  The LIBRARY lemma supplies smoothness and `mfderiv f = omega`.
This assembly is sorry-free.

## Dependency layers

* **Layer 1:** `apm_t96A08_piecewise_lineIntegral_fundamental` (one LIBRARY
  program).
* **Layer 2 (already compiled):** choice, well-definedness, and final assembly.

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

The sole `sorryAx` enters through the one top-level LIBRARY lemma.  The main
theorem has no direct `sorry`.


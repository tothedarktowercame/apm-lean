# Genuine smooth projected rank chart — 2026-09-09

GO fixture: `/tmp/SardGenuineSmoothProjectedRankChart.lean`.
Proposed module: `ConstructionTargets/SardGenuineSmoothProjectedRankChart.lean`.

The old `SardProjectedSmoothLocalRankChart` excludes genuine infinity because
its local regularity premise is pointwise. This theorem instead assumes global
`ContDiff real infinity f`, sets L to the actual fderiv at x, and constructs the
projected ImplicitFunctionData from the existing complemented strict-derivative
producer. Its range R and kernel G retain the existing orthogonal-projection
representations. Every defining field is returned explicitly.

Both fields are smooth on the original open chart source: composition with the
range projection for the left field, and the kernel projection for the right.
`SardSmoothNeighborhoodImplicitChart.exists_smooth_implicit_chart` supplies the
basepoint-preserving restriction, source inclusion, original forward map,
inverse agreement on the restricted target and genuine infinity smoothness in
both directions. The output also states the first-coordinate identity.

The final conjunct invokes the actual residual-slice consumer with the
orthogonal-complement target projection. It proves smoothness at each point
of each slice's actual target domain. No chart, inverse regularity or nullity
premise is assumed. Target finite dimensionality is unnecessary here: the
finite-dimensional source already gives finite-dimensional derivative range.
Thus the result includes the requested finite-dimensional target case.

This is only a chart producer. Positive-rank residual criticality and image
nullity, compatible local smooth induction and base cases, critical-set
coverage and manifold transport remain. It proves neither unconditional Sard
nor the frozen t93A04 regular-value theorem. The other four consumers are
prospective downstream consumers, not closed problems.

Promotion scope: this .lean module and this .md note only. Verify fixture and
source pins, copy the fixture, compile both fixture and promoted module, run
`lake build ConstructionTargets.SardGenuineSmoothProjectedRankChart`, verify
zero executable placeholders and standard-only axioms, run git diff --check,
and commit only the two scoped files. Do not modify the earlier chart API,
the frozen consumer, DAG or ledger.

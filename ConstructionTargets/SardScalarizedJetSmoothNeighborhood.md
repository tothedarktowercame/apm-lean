# Scalarized jets supply genuine smooth implicit neighborhoods

Read-only probe, 2026-09-09, codex-12.

The theorem `SardScalarizedJetSmoothNeighborhoodProbe.exists_scalarized_jet_smooth_chart`
uses global `ContDiff ℝ ∞ f`, a finite order i, fixed directions v, a scalar
continuous linear functional ell, and a nonzero next-jet evaluation at x in
direction h. Here infinity is genuine smoothness, not analytic outer top.

The existing strict-derivative and defining-field producers construct exactly
g(y)=ell(iteratedFDeriv ℝ i f y v), L=fderiv ℝ g x, G=ker L,
and ImplicitFunctionData with leftFun=g, leftDeriv=L, rightFun the orthogonal
projection onto G, rightDeriv that projection, and pt=x. The existing
remaining-order producer proves global smoothness of g from infinity+i=infinity.
The right field is smooth because the projection is continuous linear.

Take U to be the original open chart source, which contains the basepoint.
These derived field hypotheses feed the reviewed
SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_implicit_chart.
The returned restriction contains x, stays inside the original source, has the
original forward map and agrees with the original inverse on its target, and
is genuinely smooth in both directions. Its inverse and the original smooth
f feed SardProjectedChartResidualSlicesContDiffOn at infinity, with projection
ell. The result includes smoothness at every admissible point of every slice.
No extra neighborhood smoothness or nullity assumptions are introduced.

Explicit completeness instances follow the existing defining-field API and
use its canonical kernelCompleteSpace producer. No kernel representation is
changed. The full theorem compiles without placeholders or warnings and has
only propext, Classical.choice and Quot.sound as axioms.

Prospective implementation scope: ConstructionTargets/SardScalarizedJetSmoothNeighborhood.lean
and ConstructionTargets/SardScalarizedJetSmoothNeighborhood.md. No source,
ledger, or DAG edits were made by this probe.

Remaining consumer work: connect zero-level containment and source dimension
drop to a compatible local critical-nullity induction. The arbitrary-C1
hindOne interface, base cases, local nullity and manifold transport are not
closed here. Frozen t93A04 retains its one executable placeholder.

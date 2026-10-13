# Blueprint for t96A02

## Triage

Verdict: **true and faithful**.

The registered theorem says exactly that every continuous self-map of the
concrete space `ProjectivePlaneWedge` has a fixed point.  This model is the
coinduced-topology quotient obtained by identifying the images of the centers
of two copies of the standard polygon model of `RP²`, so it matches the space
in `problem.md`.

Attempts to break the statement do not produce a counterexample.  The space is
nonempty, and a constant map fixes its constant value.  The identity fixes every
point.  More generally, the wedge is connected and has no positive-degree
rational homology, so every self-map has rational Lefschetz number `1`; the
Lefschetz fixed-point theorem then rules out a fixed-point-free map.  No repair
is needed.

There are no new definitions.  `ProjectivePlaneWedge` comes from
`ConstructionTargets.StatementSurfaceModels`, and `HasLefschetzNumber` comes
from the sorry-free vocabulary module `ConstructionTargets.RationalLefschetz`.
The two open statements deliberately use the same forms as
`t99A03_wedge_lefschetz_number` and
`t99A03_wedge_fixed_point_of_lefschetz`, specialized from its fourfold wedge to
the twofold wedge.  This lets the same rational-homology and Lefschetz
foundations close both consumers.

## Remaining lemmas

### `t96A02_wedge_lefschetz_number` — LIBRARY

**Statement.** Every continuous self-map of `ProjectivePlaneWedge` has rational
Lefschetz number `1`.

**Why true.** `RP²` has zero reduced rational homology.  Reduced homology of a
point wedge is the direct sum of the reduced homologies of its summands, so the
wedge also has zero reduced rational homology.  It is connected, hence only
`H₀ ≅ ℚ` contributes to the Lefschetz number, and every self-map induces the
identity on that one-dimensional `H₀`.  The alternating trace is therefore
`1`.  The topology worklist records the shared missing foundations as
`ConstructionTargets.ProjectivePlaneRationalHomology.acyclic` and
`ConstructionTargets.PointWedgeRationalHomology.acyclic`; the final trace
calculation is the recorded `projectivePlaneWedge_lefschetz_one` step.

**Estimate.** LIBRARY program: 1000–2000 lines across the shared RP² homology
and point-wedge Mayer–Vietoris foundations, followed by an 80–160 line trace
specialization.

**Depends on.** No other blueprint lemma.

**Truth check.** The standard cellular chain complex over `ℚ` has the
degree-two attaching map multiplication by `2`, which is invertible over `ℚ`;
thus positive reduced rational homology vanishes.  Wedge direct sums preserve
that vanishing.  Both the identity and every constant map consequently have
Lefschetz number `1`, checking the two simplest endpoint maps.

### `t96A02_wedge_fixed_point_of_lefschetz` — LIBRARY

**Statement.** If every self-map of `ProjectivePlaneWedge` has Lefschetz number
`1`, then every such self-map has a fixed point.

**Why true.** The wedge of two finite projective-plane CW complexes at a point
is a finite compact polyhedron.  Apply the rational Lefschetz fixed-point
theorem to each map; the supplied Lefschetz number is `1`, hence nonzero.  The
shared missing theorem is the topology program recorded as
`ConstructionTargets.LefschetzCompactPolyhedron.fixedPointOfNonzeroLefschetz`
(also recorded as `lefschetz_fixedPoint_compactPolyhedron`).  This genuinely
large foundation is stated once rather than decomposed into proxy lemmas.  The
homology conclusion is passed in as a hypothesis, exactly as in the t99A03
blueprint, so the two programs can be developed independently.

**Estimate.** LIBRARY program: 2000–5000 lines for the shared compact-polyhedron
Lefschetz theorem, plus 30–60 lines to exhibit this quotient as the relevant
finite polyhedron.

**Depends on.** Receives the conclusion of
`t96A02_wedge_lefschetz_number` as a hypothesis; it does not depend on that
lemma's proof.

**Truth check.** The supplied value is exactly `1`, so its nonzero condition is
immediate.  The space has a concrete wedge point, and the constant-map case
fixes its image, agreeing with the theorem.  The finite-CW model is obtained by
wedging the usual one-cell/one-two-cell models of the two copies of `RP²`.

## Dependency layers

* **Layer 1 (parallel):** `t96A02_wedge_lefschetz_number` (LIBRARY) and
  `t96A02_wedge_fixed_point_of_lefschetz` (LIBRARY, taking the first lemma's
  conclusion as a hypothesis).
* **Layer 2:** `apm_t96a02`, a sorry-free one-line assembly.

There are **two open lemmas**, both shared LIBRARY foundations.  I have no
doubt about their mathematical truth.  The only material risk is implementation
size: Mathlib does not presently expose the needed compact-polyhedron
Lefschetz theorem, and the quotient model still has to be connected to a finite
CW/polyhedron presentation.

## Compilation and axioms

`Blueprint.lean` was compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t96A02/Blueprint.lean
```

The final output of `#print axioms apm_t96a02` was:

```text
'apm_t96a02' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

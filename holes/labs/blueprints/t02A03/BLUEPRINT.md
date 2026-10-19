# Blueprint for t02A03

## Triage

Verdict: **true and faithful**.

The registered theorem states both geometric deformation-retract models from
the problem: the solid torus minus its core is homotopy equivalent to
`Circle × Circle`, and the explicit genus-two handlebody minus the chosen
core is homotopy equivalent to the quotient model `T² ∨ S¹`.  Its remaining
conjuncts compute exactly `π₁(T²)`, `π₁(T² ∨ S¹)`, and the degreewise
integral singular homology asserted in `problem.md`.

I tried the relevant degeneracies before retaining the statement.  The disk
radius and tube radius are positive.  The two planar core circles have nearest
separation `2/5`, which is larger than the tube radius `1/4`; hence the
left core does not enter the right tube.  Nevertheless the two closed tubes
overlap around the origin, so the model is connected and the second handle
cannot disappear as an empty summand.  Deleting the left core makes its radial
coordinate nonzero, giving the meridional circle and hence a torus factor.
These checks agree with the hand deformation-retraction argument in
`informal-solution.md`.  No counterexample is recorded by the solve loop;
the topology ledger marks the statement faithful and identifies only the
geometric equivalence as unfinished.

## Reused sorry-free work

`Blueprint.lean` retains the compiled definitions and proofs from
`Main.lean`.  In particular:

* `T02A03ClosedPuncturedDiskTorus.t02a03_closed_punctured_disk_torus`
  supplies the first geometric homotopy equivalence.
* `FundamentalGroupProduct` and `CircleUniversalCover` supply the torus
  fundamental-group computation.
* `PointWedgeQuotient`,
  `GenericTargetNaturalSourceReconstruction`,
  `TorusCircleWedgeMayerVietoris`, and
  `BoundaryTorusHurewiczIsomorphism` supply the wedge fundamental group and
  all singular-homology computations.

I searched `ConstructionTargets/` for
`leftTubeMinusCoreHomotopyEquivTorus`,
`rightTubeMinusLeftCore...HomotopyEquiv`, and
`geometricYHomotopyEquivGenericWedge`.  The relevant existing files are
sorry-free, including `T02A03LeftTubePuncturedModel.lean` and
`T02A03GeometricTubeDeformation.lean`, but they do not expose the final
global equivalence required here.  The ledger and
`~/notes/closer/audits/t02A03.md` confirm that about 1,800 lines of local
collision analysis were banked without completing the compatible global
deformation/gluing step.

## Remaining lemmas

### Split of `apm_t02a03_geometricY_homotopyEquiv_genericWedge` (2026-10-19)

Two lemma-1 runs: the first failed on a Codex 429; the second returned PARTIAL
after one minute with only `spine_nonempty` and `W = leftTube ∪ rightTube`
(not banked: neither leaf below needs them). The lemma is now proved by
`HomotopyEquiv.trans` through the intermediate space

`apm_t02a03_shellY = {p ∈ W | 1/4 ≤ infDist p C}`,

which lies in `geometricY` (distance > 0 from the closed core) and is compact.

### `apm_t02a03_geometricY_homotopyEquiv_shellY` — LIBRARY

**Statement in words.** Pushing points of the left tube radially off the
deleted core is a strong deformation retraction of `geometricY` onto `shellY`.

**Proof sketch.** Write `q = (x + 6/5, y)` and `s = ‖q‖`. Inside the left tube
`s ≥ 3/4 > 0`, the nearest core point is `c(p) = (-6/5,0,0) + (q/s, 0)` and
`infDist p C = ‖p - c(p)‖ = sqrt((s-1)² + z²)` (the circle has reach 1 > 1/4).
Set `ρ(p) = c(p) + (1/4)(p - c(p))/‖p - c(p)‖` when `infDist p C ≤ 1/4`, and
`ρ(p) = p` otherwise; both branches agree at distance `1/4`, so glue with
`Continuous.if_le`. The homotopy moves along the same normal segment, with
distance from the core going from `‖p - c(p)‖` to `1/4`, so it stays in `W`
and never meets `C`. Package as a `HomotopyEquiv` with the inclusion
`shellY → geometricY`.

**Expected size.** 150–250 lines; most of it is the closed-form `infDist` to
the planar circle.

### `apm_t02a03_shellY_homotopyEquiv_genericWedge` — LIBRARY

**Statement in words.** `shellY` has the homotopy type of the production
`TorusCircleWedgeOpenCover.GenericWedge`.

**Why true.** `shellY` is the boundary torus `{infDist p C = 1/4}` together with
`R \ L°` (right tube minus the open left tube). The right core stays at
distance at least 2/5 from `C`, so it lies in `R \ L°`, which retracts onto it.
The two pieces meet in the patch of the torus inside `R`, a disk. A torus and
a circle-homotopic piece glued along a disk give `T² ∨ S¹`.

**Suggested route.** Avoid closed-cover gluing (Mathlib has no API for it).
Build an explicit deformation of `shellY` onto an embedded `T² ∪ arc ∪ S¹`
spine, then compare that compact spine with `GenericWedge` via
`Continuous.quotient_lift` and `Continuous.homeoOfEquivCompactToT2`. This is
still the larger piece; `ConstructionTargets.T02A03ClosedPuncturedDiskTorus`
is imported and may supply the torus model.

**Banked geometry caveat (still applies).** `T02A03GeometricTubeCover` uses
centers `(±1,0,0)`, not the registered `(±6/5,0,0)`; its tube subtypes have
different types and cannot supply leaves here.

### `apm_t02a03_geometricY_homotopyEquiv_genericWedge` — proved assembly

`e.trans f` of the two leaves above.

### `apm_t02a03_transport_genericWedge_homotopyEquiv` — proved, independent

**Statement in words.** Given a homotopy equivalence from the registered
geometric complement to `GenericWedge`, transport its target across
`apm_t02a03_productionHomeomorph` to the registered quotient `apm_t02a03_Y`.

**Expected size.** 5–10 lines.  It uses
`Homeomorph.toHomotopyEquiv` and `ContinuousMap.HomotopyEquiv.trans`.
The geometric equivalence is an explicit hypothesis, so this theorem can be
checked and proved without inheriting the LIBRARY lemma's `sorryAx`.

### `apm_t02a03_geometricY_homotopyEquiv_wedge` — proved assembly

Applies the transport lemma to
`apm_t02a03_geometricY_homotopyEquiv_genericWedge`.  This retains the original
library-lemma name and statement for the byte-identical main-theorem assembly,
but the declaration itself contains no `sorry`.

## Assembly and dependency layers

The main theorem uses the already proved first geometric equivalence, the
single LIBRARY lemma above, and the already proved bridge computations.  It
contains no `sorry`.

* **Layer 0:** `apm_t02a03_geometricY_homotopyEquiv_shellY` and
  `apm_t02a03_shellY_homotopyEquiv_genericWedge` (LIBRARY, independent).
* **Layer 1:** the proved assembly `apm_t02a03_geometricY_homotopyEquiv_genericWedge`,
  and independently the proved generic transport lemma.
* **Layer 2:** the sorry-free `apm_t02a03_geometricY_homotopyEquiv_wedge`
  assembly.
* **Layer 3:** the already compiled main-theorem assembly.

Thus the blueprint still has **one admitted lemma**, now exactly the geometric
construction, and no artificial self-carrying hypothesis.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A03/Blueprint.lean
```

The output of `#print axioms apm_t02a03` is:

```text
'apm_t02a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The sole warning identifying `sorry` is at the LIBRARY lemma.  The main
theorem and every reused bridge declaration have no direct `sorry`.

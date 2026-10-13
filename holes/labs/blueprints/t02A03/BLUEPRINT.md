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

## Remaining lemma

### `apm_t02a03_geometricY_homotopyEquiv_wedge` — LIBRARY

**Statement in words.** The explicit complement of the left core in the
closed quarter-neighborhood of the two-circle spine is homotopy equivalent to
the concrete quotient wedge `T² ∨ S¹`.

**Why true.** Split the complement into its left- and right-tube pieces.  The
left piece minus its core radially retracts to `T²`; the right piece is
disjoint from the deleted core and retracts to its core circle.  Their
lens-shaped overlap is contractible.  Choose these equivalences compatibly on
the overlap and glue their homotopies, yielding the wedge.  Finally transport
the production `GenericWedge` model across
`apm_t02a03_productionHomeomorph`.

This is the global construction tracked as
`ConstructionTargets.T02A03GeometricTubeDeformation.geometricYHomotopyEquivGenericWedge`
in the topology worklist.  It is deliberately one LIBRARY lemma: the audit
estimates the missing compatible deformation/gluing implementation at
200–400 lines (after substantial banked local geometry), so dividing it into
small theorem shells would conceal rather than separate the missing
foundation.

**Expected size.** 300–500 lines for the final construction, reusing the
existing local geometry; potentially more if a specialized closed-cover
homotopy-gluing API must be developed.

**Dependencies.** Only the definitions and the imported, sorry-free
construction-target modules.  There are no other admitted blueprint lemmas.

**Truth check.** Besides the distance and nonemptiness checks in triage, the
model was checked by hand in the two extreme local regions: over the left
core, puncturing a normal disk gives `(D² \ {0}) × S¹ ≃ T²`; over the
right core, the deleted set is absent because `2/5 > 1/4), leaving a solid
torus `≃ S¹`.  At the connecting lens the origin is present and is outside
both cores, so contraction of the overlap does not cross the deleted curve.
The remaining difficulty is formal compatibility/continuity, not a doubtful
mathematical assertion.

## Assembly and dependency layers

The main theorem uses the already proved first geometric equivalence, the
single LIBRARY lemma above, and the already proved bridge computations.  It
contains no `sorry`.

* **Layer 1:** `apm_t02a03_geometricY_homotopyEquiv_wedge` (LIBRARY).
* **Layer 2:** the already compiled main-theorem assembly.

Thus the blueprint has **one admitted lemma** and no artificial
self-carrying hypothesis.

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

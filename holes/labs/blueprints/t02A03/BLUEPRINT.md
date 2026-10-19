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

### `apm_t02a03_geometricY_homotopyEquiv_genericWedge` — LIBRARY

**Statement in words.** The explicit complement of the left core in the
closed quarter-neighborhood of the two-circle spine is homotopy equivalent to
the production quotient `TorusCircleWedgeOpenCover.GenericWedge`.

**Why true.** Split the complement into its left- and right-tube pieces.  The
left piece minus its core radially retracts to `T²`; the right piece is
disjoint from the deleted core and retracts to its core circle.  Their
lens-shaped overlap is contractible.  Choose these equivalences compatibly on
the overlap and glue their homotopies, yielding the wedge.  Finally transport
the production `GenericWedge` model across
`apm_t02a03_productionHomeomorph`.

This is the genuinely geometric boundary.  A useful implementation should
avoid a closed-cover gluing theorem (Mathlib has no suitable API) and instead
construct one explicit strong deformation retraction onto an embedded
`T² ∨ S¹`: use radial normalization in the punctured left normal disk,
core contraction on the right tube, and a single-coordinate piecewise formula
through the lens.  The continuity tools to use are `Continuous.if_le` or
`ContinuousOn.piecewise`; package the resulting two continuous maps and
homotopies directly as `ContinuousMap.HomotopyEquiv`.  For the final compact
embedded spine comparison, use `Continuous.quotient_lift` (or
`IsQuotientMap`) out of the sum quotient and
`Continuous.homeoOfEquivCompactToT2` for the inverse.

This leaf cannot honestly be subdivided further in the present file because
the named banked geometry is not geometry for the registered statement.
`T02A03GeometricTubeCover` defines centers `(-1,0,0)` and `(1,0,0)`, so both
cores contain the origin.  The registered theorem and this blueprint define
centers `(-6/5,0,0)` and `(6/5,0,0)`, whose cores are disjoint and separated
by `2/5`.  Consequently its `GeometricY`, tube subtypes, radial maps, and
collision lemmas have different types and cannot supply leaves here.  Porting
that development or writing the explicit deformation is a genuine 300–600
line foundation, not a 30–150 line proof boundary that can be exposed merely
by theorem shells.

**Expected size.** 300–600 lines for an explicit global deformation and
embedded-spine comparison.  A closed-cover gluing API would be a larger
foundation and is not recommended.

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

* **Layer 1:** `apm_t02a03_geometricY_homotopyEquiv_genericWedge` (LIBRARY),
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

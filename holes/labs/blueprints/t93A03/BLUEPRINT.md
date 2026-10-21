# Blueprint for t93A03

## Triage and repair

Verdict on `problems/t93A03/lean/Main.lean`: **unfaithful (vacuous)**.

The source asks only to prove that
`(S¹ × S²) # (S¹ × S²)` is not simply connected.  The old Lean statement
instead assumes

```text
T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine
```

where `T93A03Spine` is a wedge of two circles.  This is false: the left side
is a closed orientable three-manifold with nonzero `H₂` (indeed `ℤ²`) and
`H₃` (`ℤ`), whereas a wedge of circles has zero homology in those degrees.
Consequently the hypothesis has no inhabitants for the intended connected
sum.  Moreover, the old proof obtains non-simple-connectivity directly by
transport across this false equivalence, so the hypothesis carries the core
of the requested proof.  This is exactly the counterexample recorded by
`holes/labs/statement-registry/triage-2.md`.

`RevisedMain.lean` removes both the false `hspine` hypothesis and the unrelated
extra conclusion computing the fundamental group of the auxiliary spine.  Its
conclusion is exactly the sentence in `problem.md`.  It retains the concrete
quotient construction and adds radius-two extensions of the embedded
radius-one balls.  These are exterior collars: they express the tame standard
balls implicit in the notation `#` and exclude wild embeddings for which the
quotient need not have the standard connected-sum open-cover geometry.  This
is the same collar interface already used by the reviewed `t98A02` connected-
sum blueprint.  It is geometric input, not a hypothesis containing the desired
fundamental-group conclusion.

There is no short compiled `Refute.lean`: formalizing the homology mismatch is
itself one of the large topology-library gaps.  The mathematical refutation is
the `H₂/H₃` calculation above.

Degenerate checks: the closed three-ball is nonempty, and an embedding into
`Circle × S²` rules out an empty summand.  The collar extension implies the
boundary sphere has a genuine exterior neighborhood, so the wild-ball failure
mode is unavailable.  For the standard product-chart balls the repaired
quotient is the usual connected sum, whose fundamental group is
`ℤ * ℤ = F₂`.  The registry counterexample no longer applies because no
homotopy equivalence with a one-dimensional wedge is asserted.

## Definitions

The Euclidean ball, sphere, summand, punctured summand, gluing relation,
quotient, and quotient topology are copied from `Main.lean`.  The only new
definitions are `T93A03CollarBall` (the radius-two ball) and
`t93A03DiskInCollarBall` (the literal radius-one inclusion).  No definition
packages a fundamental-group or non-simple-connectivity conclusion.

The blueprint imports `ConstructionTargets.CollaredConnectedSumHomology` and
uses its `BallCollar`, `ConnectedSum`, `HasStandardCover`, and
`BallCollar.connectedSum_standardCover` interfaces.  It also retains
`ConstructionTargets.PointWedgeVanKampen`, whose generic groupoid machinery
is the closest existing foundation for the one remaining van Kampen leaf.

## Lemmas

### `T93A03PiOne.quotientHomeomorph` (P1) — leaf

The frozen quotient is homeomorphic to `ConnectedSum c₁ c₂` when the
collars' small maps are `φ₁,φ₂`.  Estimate: 40–80 lines.  Follow
`T98A02Adapter.quotientHomeomorph` and
`PointWedgeQuotient.quotientHomeomorphOfRelIff`.  The relation orientation is
identical (left boundary to right boundary); `dist u 0 = ‖u‖` reconciles the
puncture predicates.  Independent of P2–P6.

### `T93A03PiOne.puncturedGeometry` (P2) — leaf

Every three-ball collar in `S¹ × S²` has open radius-two image and
path-connected puncture.  Estimate: 80–150 lines.  Build the usual product
manifold using `ChartedSpace.prod` and `IsManifold.prod`, then change its model
from `ModelProd (E 1) (E 3)`/the sphere model to `E 3` along the coordinate
continuous linear equivalence; apply
`BallCollar.largeInterior_isOpen` and
`BallCollar.punctured_pathConnected 3 (by omega)`.  This model-change is the
risky implementation point: Mathlib has product charts, but no searched
one-line `ChartedSpace.comp` declaration, so the atlas transport may occupy
most of the estimate.  Independent of P1 and P3–P6.

### `T93A03PiOne.puncturedPiOne` (P3) — leaf

At the explicit boundary point, the puncture has fundamental group
`FreeGroup (Fin 1)`.  Estimate: 90–150 lines.  Apply
`BallCollar.punctured_fundamentalGroup_three`, then compute the product group:
the circle factor uses
`CircleUniversalCover.circleFundamentalGroupMulEquivInt`; the sphere factor is
trivial using `SimplyConnectedOpenCover.simplyConnectedSpace_sphere_of_pole`;
finish with `PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne` and
`FundamentalGroup.fundamentalGroupMulEquivOfPathConnected` for basepoint
changes.  It takes P2's conclusions explicitly, so it can be proved in
parallel and does not acquire P2's sorry axiom.

### `T93A03PiOne.standardCoverPiOneFreeProduct` (P4) — LIBRARY

For a `HasStandardCover`, if both puncture groups at the boundary basepoint
are rank one free, the connected sum has group their free product.  Estimate:
120–150 lines.  This is the only genuinely generic van Kampen boundary.
Start from
`TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence`,
use the three homotopy equivalences stored in `HasStandardCover`, trivialize
the overlap with
`SimplyConnectedOpenCover.simplyConnectedSpace_sphere_of_pole`, and extract
the automorphism group via
`PointWedgeVanKampen.fundamentalGroupMulEquivOfSingleObjEquivalence`.
The cover inclusions are already homotopic to the two boundary maps, so the
basepoint transports are explicit rather than silently identified.
Independent of P1, P2, P5, and P6; P3's two conclusions are explicit
hypotheses.  This leaf remains marked LIBRARY because no ready-made based
two-open free-product theorem was found.

### `T93A03PiOne.twoRankOneFreeProduct` (P5) — leaf

`FreeGroup (Fin 1) * FreeGroup (Fin 1) ≃ FreeGroup (Fin 2)`.  Estimate:
20–40 lines.  Use
`PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum (Fin 1) (Fin 1)`, then
transport generators along the standard equivalence
`Fin 1 ⊕ Fin 1 ≃ Fin 2` with `FreeGroup.map_injective` and
`FreeGroup.map_surjective`.  Independent of every other leaf.

### `T93A03PiOne.transportPiOne` (P6) — leaf

A homeomorphism transports a based fundamental-group equivalence to its
inverse-image basepoint.  Estimate: 20–40 lines.  Use `FundamentalGroup.map`
for the two continuous maps (or the already proved
`BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph`).
Independent of every other leaf.

### `t93A03_collaredConnectedSum_piOne` — assembled, no `sorry`

The proof constructs the two `BallCollar`s from the supplied witnesses, uses
P2, calls `BallCollar.connectedSum_standardCover`, uses P3 and P4, composes
with P5, and transports through P1 using P6.  No leaf conclusion is obtained
by invoking another sorry'd leaf except through an explicit hypothesis.

Truth checks: `sphereBasepoint` is the first coordinate vector, so the sphere
and overlap are nonempty.  In dimension three the overlap is `S²`, exactly
the simply connected sphere needed by B6 and van Kampen.  For coordinate
balls the computation is `ℤ * ℤ = F₂`; the overlap contributes no relation.
Neither an empty set nor a dimension-zero case occurs (`Fin 3` and `Fin 2`
are inhabited).  P1 preserves the specified orientation of the quotient
relation, while equivalence closure makes no extra orientation assumption.

### `t93A03_not_simplyConnected_of_piOne_equiv` — proved

**Statement.** If `π₁(X,x)` is equivalent to `FreeGroup (Fin 2)`, then `X` is
not simply connected.

**Why true.** Under a `SimplyConnectedSpace X` instance, Mathlib makes the
loop quotient at `x` a subsingleton.  Transporting equality of the preimages
of `FreeGroup.of 0` and `1` through the equivalence contradicts
`FreeGroup.of_ne_one`.

**Estimate.** 10–20 lines; already compiled without `sorry`.

**Dependencies.** None.  It accepts the library lemma's group equivalence as
an explicit parameter, so it was checked independently.

**Truth check.** `Fin 2` is nonempty (`0 : Fin 2`), and
`FreeGroup.of_ne_one 0` verifies that the selected generator is not the
identity.  Thus there is no empty-generator edge case.

## Dependency layers

- Parallel leaves: P1, P2, P4, P5, P6, and the already proved obstruction.
- P3 is also independently provable because P2's facts are parameters.
- Assembly: the original registered LIBRARY theorem, now sorry-free.
- Final: `apm_t93a03`, unchanged, applies the obstruction.

All six new leaves state claims consumed by the assembly; none is a marker or
vacuous restatement.  P4 is the sole generic LIBRARY gap.  P1–P3 are geometric
adapters/specializations, and P5–P6 are small algebraic/functorial leaves.

## Compile and axiom gate

Commands:

```text
lake build ConstructionTargets.CollaredConnectedSumHomology
flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t93A03/Blueprint.lean
```

Both exit successfully.  Output of `#print axioms apm_t93a03`:

```text
'apm_t93a03' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` enters through the six named leaves consumed by the sorry-free
assembly (and through the imported foundation leaves B2, B3, B6, and B7 when
their implementations land).  The registered theorem and all pre-existing
definitions/statements remain byte-identical.

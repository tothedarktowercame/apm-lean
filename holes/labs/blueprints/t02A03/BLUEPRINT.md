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

### `apm_t02a03_shellY_homotopyEquiv_genericWedge` — proved assembly (split 2026-10-19)

lemma-2 returned PARTIAL with only the inclusion `shellY → geometricY` (not
banked: the assembly does not use it). The lemma is now proved from five
leaves through an explicit spine `Z = torus ∪ loop` inside `shellY`:

* `torus = {p | infDist p C = 1/4}`, the boundary torus of the left tube;
* `loop`, the planar circle `t ↦ (6/5 - (23/20) cos t, (23/20) sin t, 0)`,
  within `3/20` of the right core and touching `torus` only at
  `q0 = (1/20, 0, 0)` (`t = 0`).

`Z` is a torus and a circle meeting in one point, so it is homeomorphic to
`GenericWedge` (no arc needed). The assembly corestricts the retraction to
`Z`, gets `shellY ≃ₕ Z` (one composite is `r ≃ id`, the other is `id` on the
nose because `r` fixes `Z`), then composes with `Z ≃ₜ GenericWedge`.

Leaves (all LIBRARY, independent):

* `_aux_torus_homeomorph`: `torus ≃ₜ Circle × Circle`, `q0 ↦ (1,1)`. Parametrise
  by core angle θ and normal angle φ: `c(θ) + (1/4)(cos φ · n(θ) + sin φ · e_z)`.
  Needs the closed form `infDist p C = sqrt((s-1)² + z²)` for `s ≥ 3/4`
  (shared with `geometricY_homotopyEquiv_shellY`).
* `_aux_loop_homeomorph`: `loop ≃ₜ Circle`, `q0 ↦ 1`. Affine image of the unit
  circle.
* `_aux_loop_geometry`: `loop ⊆ W`, `1/4 ≤ infDist · C` on `loop`, and
  `torus ∩ loop = {q0}`. The point of `loop` nearest the left centre is `q0`,
  at distance `5/4`; every other point is strictly further.
* `_aux_wedge_homeomorph` (pure topology): in a Hausdorff space, `A ≃ₜ Torus`,
  `B ≃ₜ Circle`, `A ∩ B = {x}` with `x` at both basepoints give
  `A ∪ B ≃ₜ GenericWedge`. Lift `Sum A B → A ∪ B` through the quotient and
  apply `Continuous.homeoOfEquivCompactToT2`.
* `_aux_retraction`: a self-map `r` of `shellY` with image in `Z`, fixing `Z`,
  homotopic to `id`. The geometric content: the torus is fixed; `R \ L°`
  (right tube minus the open left tube) is pushed onto `loop` together with
  the patch of `torus` inside the right tube. Expected to need a further split.

### `_aux_retraction` — proved assembly (split 2026-10-19)

lemma-2 returned PARTIAL with one proved helper, banked as
`_aux_retraction_aux_of_deformation` (a strong deformation of `shellY` onto
`torus ∪ loop` gives the required `r`). The remaining gap was the whole
deformation, now split through `right = {p | infDist p (range rightCore) ≤ 1/4,
1/4 ≤ infDist p C}` (right tube minus the open left tube):

* `_aux_retraction_aux_cover` (small geometry): every point of `shellY` is on
  `torus` or in `right` (`infDist` to the two-circle spine is the minimum).
* `_aux_retraction_aux_glue` (point-set): a deformation `G` of `right` fixing
  `torus ∪ loop` extends by the identity on `torus` to a deformation `H` of
  `shellY`; the two pieces are closed and cover by `cover`.
* `_aux_retraction_aux_core` (the geometric content): `right` strong-deformation-
  retracts onto `D ∪ loop`, `D = right ∩ torus`. Suggested route in the seat
  note: a θ-cutoff straight-line collapse onto the loop away from the bite, then
  collapse of the remaining sector ball onto `D ∪` loop arc.

### `_aux_retraction_aux_core` — proved assembly (split 2026-10-19)

lemma-2 returned PARTIAL: `_aux_core_aux_concat` (`Homotopy.trans` of two
stages keeps the rel-`Z` condition) proved, the stages left as one leaf. That
leaf is now proved from two, through the intermediate subspace
`Y = Z ∨ x ≤ 4/5` (`Z = torus ∪ loop`; `θ` the right-tube angle, the bite needs
`s cos θ ≥ 23/20`, so `|θ| < 0.41`, and every tube point with `|θ| ≤ 0.82` has
`x < 4/5`):

* `_aux_core_aux_cutoff`: a homotopy `F : id ≃ m` of `right` fixing `Z`, with
  every `m p` in `Y`. The θ-cutoff straight-line collapse onto the loop offset
  `ℓ = (3/20, 0)`, `φ = 1` for `|θ| ≥ 0.82`, `φ = 0` for `|θ| ≤ 0.41`.
* `_aux_core_aux_sector`: a strong deformation retraction `H` of the subspace
  `{p // Y p}` onto `Z`, fixing `Z`. The sector piece is a 3-ball with the bite
  as a boundary dent; it collapses onto `D ∪` loop arc; identity on the rest of
  the loop.

The assembly `_aux_core_aux_stages` takes `K(t, p) = H(t, m p)`; `m` fixes `Z`
because `F` does at `t = 1`.

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

* **Layer 0:** `apm_t02a03_geometricY_homotopyEquiv_shellY` and the five
  `apm_t02a03_shellY_homotopyEquiv_genericWedge_aux_*` leaves (LIBRARY,
  independent); the proved assembly `apm_t02a03_shellY_homotopyEquiv_genericWedge`.
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

# Blueprint for t03J01

## Triage and repair

Verdict: **the registered statement is mathematically true but unfaithful; it
needs the registry's statement repair**.

There are two distinct repairs in the history of this problem.

1. The source's phrase “cuts the double torus into a twice-punctured sphere”
   is impossible. Cutting along a circle preserves Euler characteristic, while
   the genus-two surface has Euler characteristic `-2` and a sphere with two
   punctures has Euler characteristic `0`. The existing correction to a
   **twice-punctured torus** is therefore retained; it is the nonseparating
   case used by the informal solution.
2. The current Lean predicates additionally assume `HasPrimitiveClass J₁`
   and `IsNullHomologous J₂`. Those are not data in `problem.md`: they are the
   core conclusions needed to prove the two answers. `RevisedMain.lean` makes
   the smallest registry-recommended change, replacing the two predicates by
   `IsConnected (Jᶜ)` and `¬ IsConnected (Jᶜ)` respectively. The theorem's
   conclusion and all ambient surface/curve hypotheses are unchanged.

There is no `Refute.lean`, because the old theorem is not false: its extra
hypotheses make it easier. Its defect is that, for a separating curve, the
old `hcut₂.2` supplies the desired zero homology map definitionally, so the
formal proof never establishes the geometric assertion in part (b).

I checked the repaired statement against the important edge cases. An
embedded circle has nonempty complement in a closed connected surface, so the
positive connectivity hypothesis is not vacuous. A separating curve that
bounds a disc satisfies the repaired negative hypothesis even though it does
not cut the genus-two surface into two once-punctured tori; its homology class
is still zero and it still cannot be a retract, so this broader degenerate
case does not refute the conclusion. For a standard meridian of one handle,
the complement is connected and projection to that circle gives the expected
retraction. For the standard waist separating the two handles, the complement
is disconnected, the waist bounds either punctured torus, and its integral
homology class is zero.

## Reused compiled work

The blueprint retains the solve loop's sorry-free categorical argument that a
retraction makes the inclusion injective on integral `H₁`, and its zero-map
obstruction. The formerly missing circle computation is now supplied by the
sorry-free module `ConstructionTargets.CircleSingularHomology`; the blueprint
transports its explicit nonzero generator across `Circle ≃ₜ J`.

The imported sorry-free topology foundations are
`ConstructionTargets.SurfaceClassification`,
`ConstructionTargets.SurfaceSchoenflies`, and
`ConstructionTargets.ProductionOpenCoverMayerVietoris`. They are the closest
existing infrastructure for the two remaining surface-curve results, but do
not yet state either result at the required bare-subset interface.

## Remaining lemmas

### `apm_t03j01_nonseparating_curve_retract` — LIBRARY

**Statement in words.** An embedded circle in a compact connected genus-two
surface whose complement is connected is a retract of the surface.

**Why true.** Tameness/collaring for an embedded circle in a surface identifies
the cut surface as a compact genus-one surface with two boundary circles. A
classification-compatible polygon model then gives a circle-valued coordinate
whose restriction to the cut circle has degree one. Equivalently, the
nonseparating curve has a dual curve of intersection number one, hence a
primitive integral class. Represent that dual cohomology class by a map to
`S¹`, straighten its restriction to the embedded circle, and use the collar
(homotopy extension) to obtain an actual retraction.

This is a genuine library boundary rather than a small seat: Mathlib and the
current ConstructionTargets do not provide the required integral
`H¹ ≅ [X,S¹]` representability plus relative adjustment, nor an end-to-end
collar/classification theorem for a subset given only by `Circle ≃ₜ J`.

**Expected size.** 700–1,500 lines as a topology library program; the final
adapter to this statement should be 30–80 lines.

**Dependencies.** None of the other admitted lemmas. It uses the imported
surface classification/Schoenflies infrastructure and requires a new
primitive-class-to-relative-circle-map program.

**Truth check.** In the standard octagon model of the genus-two surface, take
`J` to be the `a₁` meridian. Its complement is connected and the coordinate
dual to `a₁` restricts with degree one, producing the retraction. The only
dangerous endpoint—an inessential circle bounding a disc—is excluded because
its complement is disconnected.

### `apm_t03j01_separating_curve_H1Map_zero` — LIBRARY

**Statement in words.** An embedded circle in a compact connected genus-two
surface whose complement is disconnected induces the zero map on integral
first singular homology.

**Why true.** Surface Schoenflies/collaring makes the embedded circle the common
boundary of the closures of complementary components. Orient one component;
its relative fundamental 2-chain has boundary the circle generator. Therefore
the included circle class is a boundary in the whole surface, so the inclusion
map on `H₁` is zero. The production open-cover Mayer–Vietoris sequence is the
closest existing formal route to this boundary calculation.

This matches the shared missing theorem `separating_circle_H1_zero` recorded in
the `t01A03` topology audit. That audit estimates the tameness/collar plus
Mayer–Vietoris/duality proof at 300+ lines, so it is kept as one LIBRARY result
rather than split into artificial adapters.

**Expected size.** 400–900 lines; 30–70 lines to specialize a shared
`separating_circle_H1_zero` program to this frozen functor.

**Dependencies.** None of the other admitted lemmas. It can be developed in
parallel with the positive library theorem.

**Truth check.** For the standard waist curve, either once-punctured torus is a
2-chain bounding it. For the degenerate separating curve that bounds a disc,
the disc itself supplies the same boundary, so the statement remains true.
This also checks the exact case highlighted by the registry after removal of
the old `IsNullHomologous` hypothesis.

## Assembly

The positive conjunct applies the first library lemma directly. For the
negative conjunct, the second lemma supplies the zero `H₁` map, the imported
circle computation supplies a nonzero class in `H₁(J₂; ℤ)`, and the already
compiled split-injectivity argument rules out a retraction. The main theorem
contains no `sorry`.

## Dependency layers

* **Layer 1 (parallel LIBRARY programs):**
  `apm_t03j01_nonseparating_curve_retract` and
  `apm_t03j01_separating_curve_H1Map_zero`.
* **Layer 2 (already compiled):** transport of the circle generator,
  retraction-induced injectivity, and assembly of `apm_t03j01`.

There are **two admitted lemmas**. Both are independent library-scale surface
results; all ordinary adapter work is already proved.

## Compilation and axioms

Both files compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t03J01/RevisedMain.lean
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t03J01/Blueprint.lean
```

The output of `#print axioms apm_t03j01` was:

```text
'apm_t03j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The two warnings identifying `sorry` are exactly the two Layer 1 library
lemmas. The main theorem has no direct `sorry`.

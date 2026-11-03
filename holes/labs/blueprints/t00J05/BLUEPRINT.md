# Blueprint: t00J05, arbitrary essential embedded circle

## Triage and truth checks

Verdict: **the registered theorem is true and faithful**, and is left unchanged.
It quantifies over every topological embedding `f : C(Circle, Torus)` that is
not homotopic to a constant; the blueprint adds neither smoothness nor
tameness.  `Cell f`, `CappedCylinder`, and `Necklace` are exactly the registered
quotients.  The covering conclusion is an actual `IsCoveringMap`, not merely a
homotopy model, and part (b) retains maps in both directions.

The main counterexample checks are as follows.  A constant circle is excluded
by essentiality and cannot satisfy `IsEmbedding` anyway.  A nonprimitive slope
cannot be represented by an embedded essential circle in the torus; proving
that fact is part of the missing Jordan/cutting foundation, not an extra
hypothesis.  Orientation reversal and an arbitrary primitive slope do not
change the attached-cell homeomorphism type because the circle
reparametrisation extends across the disk.  `CappedCylinder` is nonempty, and
there is no dimension-zero or empty-space degeneration.  At integer seams the
cap and cylinder are identified by the registered relation, so the standard
projection must be checked there rather than only on the two open pieces.

## Search result and route comparison

I searched Mathlib, `ConstructionTargets/`, and the existing blueprints for
Jordan, Schoenflies, annular collars, embedded-circle classification, surface
cutting, and universal/annular-cover lifts.  No usable completed theorem was
found.  `ConstructionTargets.SurfaceSchoenflies` has only closed range, finite
open/flat subcovers, transport/reparametrisation of a *supplied* local-flat
structure, and the standard zero-section chart.  It does not show that an
arbitrary embedded circle is locally flat and has no global collar, cut
surface, or classification theorem.  The t03J01, t03J02, t00A03, t01J01, and
t98J02 blueprints record the same gap.  The closest detailed lift is t91J03's
annular-circle plan.  (Corrected 2026-11-03: t91J03 closed on 2026-10-31 by a
planar crossing lemma, with no Jordan separation.  t00J05 stays blocked because
its conclusion needs a homeomorphism to a standard model, not because of t91J03.)

**Route 1 — full reduction.**  Prove topological Jordan--Schoenflies/local
flatness for arbitrary embedded circles in surfaces, obtain a global annular
collar, cut the torus, classify the cut surface as an annulus, and reglue to an
ambient normal form.  Extend the induced circle reparametrisation over the
attached disk.  This gives the `Cell f ≃ₜ Cell standardCurve` interface used in
the skeleton.  It is expensive, but its output cleanly separates the general
curve from the standard-model calculation and is reusable by the other blocked
surface problems.

**Route 2 — lifting.**  Lift `f` to the universal cover `ℝ²` or to the annular
cover associated to its primitive subgroup, then try to construct the capped
cylinder cover directly.  This proves only what t00J05 consumes and may avoid a
full compact-surface classification.  It does **not** escape planar topology:
one must prove the lifted embedded line separates the plane/strip, is disjoint
from the relevant deck translates, bounds the required fundamental strip, and
can be straightened equivariantly.  Those are Jordan--Schoenflies statements.
Estimated cost is
1500–3500 lines for the equivariant planar theorem plus 800–1500 lines for the
cover quotient, versus 2000–4000 lines for the reusable full reduction.  The
blueprint therefore chooses Route 1 and records the shared foundation proposal
in `ConstructionTargets/SurfaceEmbeddedCircleNormalization.blueprint.md`.

## Statement ladder and leaf table

| Layer | Leaf | Meaning and proposed tools | Estimate | Dependencies | Class |
|---|---|---|---:|---|---|
| 0 | `apm_t00J05_cell_normal_form` | Every essential embedded torus circle gives an attached cell homeomorphic to the standard one. Jordan--Schoenflies, annular collar, cut-surface classification, disk extension. | 2000–4000 | definitions only | **LIBRARY / missing foundation** |
| 0 | `apm_t00J05_standard_cover` | Explicit quotient projection from the capped cylinder is covering; check cylinder, cap interior, and seam charts. `Continuous.quotient_lift`, `IsCoveringMap` local criterion. | 500–900 | standard definitions | **LIBRARY** |
| 0 | `apm_t00J05_cappedCylinder_simplyConnected` | Finite exhaustion and van Kampen; each new cap kills the cylinder loop. | 400–800 | standard definitions | **LIBRARY** |
| 0 | `apm_t00J05_cappedCylinder_necklace` | Collapse connecting arcs and identify each capped band with a sphere up to homotopy. Quotient homotopies and colimit/exhaustion compatibility. | 800–1500 | standard definitions | **LIBRARY** |
| 0 | `apm_t00J05_standard_nonnull_maps` | Standard cell is `S¹ ∨ S²` up to homotopy; construct inclusion/collapse and detect their identity composite or nonzero `H₂`. | 400–700 | standard definitions | **LIBRARY** |
| 1 | `apm_t00J05_transport_cover` | Postcompose a standard cover with `H.symm`; covering maps are preserved by target homeomorphisms. | 20–40 | a supplied `H`, standard cover | ordinary |
| 1 | `apm_t00J05_transport_nonnull_maps` | Compose the maps with `H`/`H.symm`; transport any alleged null-homotopy back. | 40–70 | a supplied `H`, standard maps | ordinary |
| 2 | `apm_t00j05` | Destructure the normal-form homeomorphism and assemble the transported cover and maps with the model properties. | proved | all preceding outputs | assembly |

The five model/foundation leaves are deliberately flagged rather than assigned
false seat-sized estimates.  They cannot honestly be split into 30–150-line
proof jobs until the missing quotient/collar/cut-surface definitions and APIs
exist; inventing opaque structures whose fields restate their conclusions
would violate C2/C3.  A realistic total is **4160–8010 Lean lines**.  The shared
surface foundation accounts for roughly half and would amortise over t00A03,
t01J01, t03J01, t03J03, t03J05, t95J06, t97J02, t98J02, and t99J03.

Dependency layers are parallel: layer 0 has the normal-form and four standard
model developments; layer 1 has the two independent transport lemmas; layer 2
is the sorry-free registered assembly.

## C1–C10 record

- `cell_normal_form`: C1 primitive-slope/orientation reversal checked; C2 conclusion is a concrete homeomorphism, not a proxy; C3 only the geometric reduction, not cover/maps; C4 cutting must include both boundary components; C5 output is the exact `Cell` homeomorphism consumers use; C6 no tameness added; C7 `C(-,-)` and `≃ₜ` directions checked; C8 constant excluded and both orientations allowed; C9 no ancestor repeats; C10 prose marks the missing theorem.
- `standard_cover`: C1 seam and cap interiors checked; C2 actual `IsCoveringMap`; C3 no simple-connectivity claim; C4 local cases named; C5 returns the projection itself; C6 standard curve only at the model layer; C7 integer-to-real heights noted; C8 seam/basepoint checked; C9 distinct from StandardCurve's unproved final theorem; C10 estimate is explicit.
- `cappedCylinder_simplyConnected`: C1 infinite capped cylinder has all generator loops killed; C2 typeclass conclusion is substantive; C3 excludes cover and necklace; C4 exhaustion needs a base and successor gluing step; C5 no hidden map interface; C6 exact registered space; C7 quotient topology retained; C8 nonempty/base exhaustion checked; C9 not a repeat; C10 van Kampen route matches statement.
- `cappedCylinder_necklace`: C1 homotopy equivalence, not homeomorphism; C2 concrete registered spaces; C3 excludes cover/simple connectivity; C4 infinite exhaustion compatibility is named; C5 returns the exact equivalence; C6 matches the printed “describe” answer as repaired in Main; C7 `HomotopyEquiv` direction checked; C8 every integer sphere included; C9 not a repeat; C10 prose rejects the false homeomorphism.
- `standard_nonnull_maps`: C1 `S¹ ∨ S²` model gives both maps; C2 maps are constructed, not parameters; C3 no general-curve reduction; C4 identity-composite argument covers both nullity cases; C5 returns exact maps used by transport; C6 both printed directions retained; C7 constant-map domains checked; C8 sphere is nonempty and radius is one; C9 not a repeat; C10 prose and Lean agree.
- `transport_cover`: C1 homeomorphic target preserves covering; C2 hypothesis supplies only model cover, not conclusion; C3 20–40-line transport; C4 composition closes directly; C5 `H` direction checked; C6 no new geometric assumption; C7 continuous-map coercions explicit in proof plan; C8 nonempty irrelevant; C9 not an ancestor repeat; C10 matches file.
- `transport_nonnull_maps`: C1 nullity is invariant under homeomorphism; C2 source nonnullity does not restate transported result; C3 only transport; C4 both directions covered; C5 exact `H` supplied; C6 no narrowing; C7 constant-map source types checked; C8 basepoint choice is existential and harmless; C9 distinct from model construction; C10 matches file.

## Doubts

The registered essentiality predicate is homotopic nonconstancy, which is
correct for torus circles, but converting it to the primitive class used by
cutting requires fundamental-group or `H₁` machinery not currently packaged
for this quotient model.  The largest uncertainty in the standard model is a
clean Lean API for infinite van Kampen/exhaustions and for quotient homotopy
equivalences; the estimates may rise if those foundations must also be built.
The lifting route could be shorter if an equivariant planar Schoenflies theorem
appears, but none is present now.  These are reasons for the 4160–8010 range,
not reasons to weaken the theorem.

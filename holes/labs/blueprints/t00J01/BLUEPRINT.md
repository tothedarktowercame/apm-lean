# Blueprint for t00J01

## Triage

Verdict: **true and faithful**.

The source asks for counterexamples to three false assertions.  The registered
theorem supplies exactly those counterexamples: the concrete Klein-bottle
quotient times a circle, the identity of the metric two-sphere with Lefschetz
number `2 ≠ 1`, and the circle map induced by
`φ(θ) = θ + 2 sin θ`, with regular fibers of cardinalities three and one.
The batch registration also records the statement as graded faithful, and the
solve/topology ledgers contain no refutation.

I checked the relevant degeneracies.  The quotient and circle factors are
nonempty.  The identity really induces identity maps, so its rational traces
are `1, 0, 1`, not a detached choice of the number `2`; this branch is already
proved.  The fold is not constant and has derivative `1 + 2 cos θ`, which
changes sign.  On a fundamental interval the fiber of `1` has only the class
of `θ = 0`, while the fiber of `exp π` has three classes.  The critical points
`θ = ±2π/3` have lift-values `±(2π/3 + √3)`, which are neither selected target
modulo `2π`, so both selected values are regular.

The compiled definitions and all existing proofs from `Main.lean` are retained.
In particular, `apm_t00j01_sphere_identity_bridge` is sorry-free and uses the
already completed `ConstructionTargets.CoefficientSphereEndpoints` witnesses.
The sorry-free `CircleWindingUniqueness` and
`KleinClosedSquareOrbitInverseContinuity` construction modules are imported so
lemma seats have the existing exponential-fiber arithmetic and the endpoint of
the banked Klein quotient chain available.

## Remaining lemmas

### `apm_t00j01_klein_quotient_charts` — LIBRARY

**Statement.** The explicit coinduced quotient `apm_t00j01_Klein × Circle` is
compact, connected, and locally homeomorphic to open subsets of `ℝ³`.

**Why true.** Identify the `EqvGen` quotient with the quotient of the plane by
the standard free Klein group action.  The banked Klein action, square orbit
classification, quotient equivalence, compact-square argument, and inverse
continuity chain culminates in the imported
`KleinClosedSquareOrbitInverseContinuity` module.  What is still missing is the
local quotient-chart construction (and its product with the standard circle
charts), plus the direct connectedness assembly for this exact local quotient
type.  This is precisely the topology ledger's `quotient-surface-charts` STOP.

**Expected size.** 250–500 lines; marked LIBRARY rather than artificially
split because the compatible quotient-chart construction is one coherent
infrastructure result.

**Dependencies.** Definitions and the imported banked Klein quotient modules.

**Truth check.** The action generators are translations/reflections with no
fixed points in the generated plane action; the fundamental square is compact
and connected, and product charts have dimension `2 + 1 = 3`.  The empty-space
degeneracy cannot occur because the quotient contains the class of `(0,0)`.

### `apm_t00j01_klein_product_H3_zero` — LIBRARY

**Statement.** Assuming the preceding concrete manifold conclusion, the third
integral singular homology object of the Klein-bottle product is zero.

**Why true.** Compute `H₂(K;ℤ)=0` from the Klein polygon/Mayer–Vietoris model;
the orientation-reversing edge acts by `-1` on circle `H₁`.  Then Künneth (or a
product-cover Mayer–Vietoris calculation) gives `H₃(K×S¹;ℤ)=0`.  No current
sorry-free `ConstructionTargets` module provides this concrete computation;
the topology audit estimates it at 350–700 lines.  The chart conclusion is an
explicit hypothesis, following the blueprint rule that a dependent seat may
assume the producer's conclusion and therefore work in parallel.

**Expected size.** 350–700 lines; LIBRARY.

**Dependencies.** The conclusion of `apm_t00j01_klein_quotient_charts`, passed
as `_hM` rather than referenced as a theorem.

**Truth check.** A closed connected nonorientable three-manifold has zero top
integral homology.  Concretely, the Klein bottle has `H₂=0`, while the only
possible degree-three Künneth term is `H₂(K) ⊗ H₁(S¹)`, hence zero.  The result
would be false for an orientable replacement such as `T²×S¹`, confirming that
the twisted relation is essential.

### `apm_t00j01_foldRegular_pi`

**Statement.** `exp π` is regular in the statement's explicit lift sense.

**Why true.** Convert exponential equality to an integral `2π` displacement
using `CircleWindingUniqueness`.  If the derivative vanished, then
`cos θ = -1/2`, hence `θ` is congruent to `±2π/3`; substitute into
`θ + 2 sin θ` and use elementary bounds on `π` and `√3` to contradict the
target congruence.

**Expected size.** 70–130 lines.

**Dependencies.** Definitions and compiled lift/derivative lemmas only.

**Truth check.** At the evident root `π`, the derivative is `-1`.  At the two
other roots, they lie strictly away from the turning points because the local
maximum is above `π` and the local minimum below `π`.

### `apm_t00j01_foldRegular_one`

**Statement.** `1` is regular in the statement's explicit lift sense.

**Why true.** Use the same critical-point classification.  At a critical
point the lift value is congruent to `±(2π/3 + √3)`, never `0 mod 2π`.

**Expected size.** 60–110 lines.

**Dependencies.** Definitions and compiled lift/derivative lemmas only.

**Truth check.** The sole fundamental-interval root is `0`, where the compiled
derivative calculation gives `3 ≠ 0`.  Endpoint representatives `-π` and `π`
do not map to `1`.

### `apm_t00j01_foldFiberCard_pi`

**Statement.** The fiber over `exp π` has `Nat.card = 3`.

**Why true.** Represent each circle point by an angle in a half-open interval.
Split that interval at the two critical angles `±2π/3`.  Strict monotonicity
from the sign of `1 + 2 cos θ`, the intermediate value theorem, and endpoint
values show exactly one root on each of the three monotone arcs.  Exponential
fiber arithmetic removes all other `2π` translates, and an explicit
three-element equivalence finishes the `Nat.card` computation.

**Expected size.** 100–150 lines.

**Dependencies.** Definitions, `CircleWindingUniqueness`, and the compiled
lift/derivative lemmas.  It deliberately does not depend on the regularity
lemma, so both seats can proceed in parallel.

**Truth check.** `φ(π)=π`; moreover `φ(2π/3)=2π/3+√3>π`, producing the other
two crossings around the fold.  The three monotone branches have signs
`+, -, +`, so the signed count remains one while the unsigned count is three.

### `apm_t00j01_foldFiberCard_one`

**Statement.** The fiber over `1` has `Nat.card = 1`.

**Why true.** On `[-π,π]`, `θ` and `sin θ` have the same sign, so
`θ + 2 sin θ = 0` only at zero.  The exponential equality permits translates
by `2π`; the half-open representative bounds exclude every nonzero translate.
Build an equivalence of the fiber subtype with `Fin 1` and simplify its card.

**Expected size.** 70–130 lines.

**Dependencies.** Definitions, `CircleWindingUniqueness`, and the compiled
lift identity only.

**Truth check.** `θ=0` is the compiled exhibited preimage.  For `θ>0` in the
fundamental interval the lift is positive, and for `θ<0` it is negative, so
there is no second root; the two endpoints represent one circle point and map
to `exp π`, not `1`.

## Assembly and dependency layers

The main theorem contains no `sorry`: it pairs the chart lemma with the H3
lemma, reuses the completed sphere bridge, and inserts continuity plus the four
circle facts directly.

- **Layer 1 (parallel):** `apm_t00j01_klein_quotient_charts`,
  `apm_t00j01_klein_product_H3_zero` (with the chart conclusion as a
  hypothesis), `apm_t00j01_foldRegular_pi`,
  `apm_t00j01_foldRegular_one`, `apm_t00j01_foldFiberCard_pi`, and
  `apm_t00j01_foldFiberCard_one`.
- **Layer 2 (already compiled):** the main theorem assembly after the six
  Layer 1 bodies are supplied.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00J01/Blueprint.lean
```

The output of `#print axioms apm_t00j01` was:

```text
'apm_t00j01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The six warnings identifying `sorry` are exactly the six named remaining
lemmas.  The theorem assembly and all reused declarations have no direct
`sorry`.

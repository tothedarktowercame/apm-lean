# t97A01 blueprint

## Triage verdict: true and faithful

The frozen Lean statement is the literal invariant computation requested by
the informal problem.  Its first quotient has boundary word `a a b b c c`,
and its second has boundary word `a b a⁻¹ b⁻¹ c c`.  Both are closed
nonorientable genus-three surfaces.  Thus each has

`H₀ = ℤ`, `H₁ = ℤ² × ZMod 2`, and `Hₖ = 0` for `k ≥ 2`;

the second has the displayed one-relator fundamental group.  No statement
repair is warranted.

Degenerate-case checks: the disk is nonempty (its centre is a point), both
relations pair all six boundary arcs, and all six polygon vertices are in one
generated equivalence class.  In particular, neither quotient is the empty or
zero-space degeneration.  The degree-two cellular boundary is nonzero in both
presentations: `(2,2,2)` for `aabbcc`, and `(0,0,2)` for
`aba⁻¹b⁻¹cc`.  Both maps `ℤ → ℤ³` are injective, so the claimed vanishing of
`H₂` passes the endpoint check.  Their Smith normal form is `diag(2,0,0)`,
which gives exactly two free generators and one element of order two in `H₁`.

The old solve-loop obstruction is genuine: Mathlib has no ready-made theorem
which identifies singular homology or the fundamental group of these literal
`EqvGen` polygon quotients.  The newer `ConstructionTargets` files now provide
the radial open cover, the puncture/outer deformation data, the overlap-circle
model, the boundary three-loop homeomorphisms, production Mayer--Vietoris
infrastructure, and open-cover fundamental-groupoid descent.  They do not yet
provide the final induced boundary-map calculation or the resulting invariant
theorems.  Every imported `ConstructionTargets` source used by the blueprint
was checked to contain no `sorry`.

## Definitions block

`Blueprint.lean` repeats the frozen disk, edge parametrization, two relations,
quotient spaces, coinduced topologies, singular-homology abbreviation,
basepoint, and relator.  These are definitions, not chosen certificates; no
predicate is defined to be a desired conclusion.

## Lemma 1 — `apm_t97a01_polygon_singular_homology` (LIBRARY)

Statement in words: simultaneously compute all integral singular homology
groups of the two literal six-edge quotients.

Why true: use the radial two-open-cover packages.  The inner part contracts;
the punctured/outer part deformation-retracts to the boundary quotient, which
the banked three-loop homeomorphisms identify with a wedge of three circles;
the overlap is homotopy equivalent to a circle.  Apply the production
Mayer--Vietoris sequence.  Splitting the overlap generator into its six ordered
arcs makes its map on `H₁` the abelianized boundary word.  It is `(2,2,2)` for
`aabbcc` and `(0,0,2)` for `aba⁻¹b⁻¹cc`.  Smith reduction gives cokernel
`ℤ² × ZMod 2`; injectivity gives `H₂ = 0`, while exactness and the homology of
the pieces give `H₀ = ℤ` and vanishing above degree two.

Closest banked modules:

- `ConstructionTargets.PolygonRadialOpenCoverPackages`
- `ConstructionTargets.PolygonOverlapHomotopyEquivCircle`
- `ConstructionTargets.PolygonBoundaryThreeLoopHomeomorphisms`
- `ConstructionTargets.ProductionOpenCoverMayerVietoris`

What is missing: the induced `H₁` boundary-word calculation, wedge-of-three-
circles singular homology in the exact required coordinates, Smith-cokernel
assembly, and transport back to both frozen quotient types.

Estimated size: 800–1600 lines.  This is intentionally one LIBRARY task rather
than two conclusion-shaped tasks, because the two computations share all the
cover, wedge, Mayer--Vietoris, and Smith-normal-form machinery.

Dependencies: none of the other blueprint lemmas.  It depends only on the
definitions and imported sorry-free construction modules.

Truth check: hand cellular/Mayer--Vietoris computation; injectivity checked for
both vectors; Smith normal forms checked by the unimodular basis changes
`(a,b,c) ↦ (a,b,a+b+c)` and the evident third-coordinate basis for `(0,0,2)`.

## Lemma 2 — `apm_t97a01_torusRP2_fundamentalGroup` (LIBRARY)

Statement in words: the fundamental group of the literal torus-crosscap
hexagon quotient at the centre is the free group on `a,b,c` modulo the one
relation `a b a⁻¹ b⁻¹ c c`.

Why true: apply the banked two-open fundamental-groupoid van Kampen machinery
to the radial cover.  Contractibility of the inner piece kills its vertex
group.  The outer piece retracts to the three-circle boundary quotient, whose
fundamental group is free on the three paired-edge orbits.  Track the positive
overlap-circle loop through the six boundary arcs.  The reversal flags on the
first two pairs yield `a,b,a⁻¹,b⁻¹`; the same-orientation final pair yields
`c,c`.  Quotienting by the normal closure of that image is exactly the stated
`PresentedGroup`.  Finally transport the radial-cover basepoint to the frozen
centre basepoint.

Closest banked modules:

- `ConstructionTargets.PolygonSurfacePiOne` (pairing data, one-vertex proof,
  radial cover and deformation machinery)
- `ConstructionTargets.PolygonBoundaryThreeLoopHomeomorphisms`
- `ConstructionTargets.FiniteCircleWedgeFundamentalGroup`
- `ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout`

What is missing: the path-level ordered boundary-word theorem, reduction of
the pseudopushout to the normal-closure quotient, and the final basepoint and
generator-coordinate transports.

Estimated size: 600–1200 lines.  This is a genuine LIBRARY result, not a fake
chain of small wrappers.

Dependencies: none of the other blueprint lemmas.  It depends only on the
definitions and imported sorry-free construction modules.

Truth check: hand van Kampen computation on the punctured torus plus Möbius
band decomposition.  Abelianizing the resulting relation gives `2c = 0`,
independently agreeing with Lemma 1's `H₁` calculation.

## Final assembly and dependency layers

The main theorem contains no `sorry`; it destructures Lemma 1 and appends
Lemma 2.

- Layer 1, fully parallel: `apm_t97a01_polygon_singular_homology` and
  `apm_t97a01_torusRP2_fundamentalGroup`.
- Layer 2: the already-complete proof of `apm_t97a01`.

Lemma count: 2, both marked LIBRARY because each exceeds the normal
30–150-line lemma-seat range.

## Compilation and axioms gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t97A01/Blueprint.lean
```

Result: exit 0.

Exact `#print axioms apm_t97a01` output:

```text
'apm_t97a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` reaches the final theorem only through the two named top-level
library lemmas.

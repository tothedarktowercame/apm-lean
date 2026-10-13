# Blueprint for t92J05

## Triage

Verdict: **true and faithful**. No statement repair is needed.

The source asks for the fundamental groups of `RP²`, `S² × S¹`, and the
closed oriented surface of genus two. The Lean theorem uses the concrete real
projectivization, concrete metric spheres, and a space equipped with a
homeomorphism to `ConstructionTargets.Surfaces.Surface true 2`. Its three
answers are respectively `Z/2`, `Z`, and the standard four-generator
one-relator surface group. This is exactly the informal statement. The batch
registration also grades this revised homeomorphism-based genus encoding
faithful.

I checked the relevant degeneracies. All three concrete spaces are nonempty,
and every clause quantifies over an actual basepoint, so there is no empty-type
vacuity. The radius in both metric spheres is `1`, not `0`; the two-sphere has
dimension two, while the circle is the complex unit circle. In the last
clause, the homeomorphism witness rules out a wrong genus, a disconnected
space, or an empty space independently of the extra manifold typeclasses. The
relator is `[a₁,b₁][a₂,b₂]`, and the compiled sanity lemmas show both that this
word is killed in the presented group and that the four displayed generators
generate it. Its abelianization has four free generators, as expected for a
genus-two surface; it is not accidentally the torus group or a trivial group.

The solve-loop and topology-loop records contain no counterexample. Their
reviewed STOP explains an implementation gap instead: Mathlib and the current
construction targets do not yet identify the concrete projectivization with
the antipodal sphere quotient, and the polygon van Kampen program has not yet
reached its final presentation theorem.

## Reused compiled work

The definitions and proved algebraic checks from `Main.lean` are retained.
The product equivalence
`apm_t92J05_fundamentalGroup_prod_equiv` and its trivial-left-factor wrapper
are fully proved. So is
`apm_t92J05_bridge_sphere_circle_fundamentalGroups`: it uses
`SimplyConnectedSphereProducts.euclideanSphere_simplyConnected` for `S²`,
`CircleMetricFundamentalGroup.metricCircleHomeomorphCircle`, arbitrary-basepoint
transport, and `CircleUniversalCover.circleFundamentalGroupMulEquivInt` for
`S¹`. The whole `S² × S¹` conclusion therefore requires no seat.

The blueprint additionally imports the sorry-free modules
`ConstructionTargets.DeckGroupQuotientFundamentalGroup` and
`ConstructionTargets.PolygonSurfacePiOne`. I searched all sorry-free
`ConstructionTargets` modules with names containing `Cover`, `Project`,
`Surface`, `Polygon`, `Fundamental`, `Sphere`, or `Circle`. The former module
already supplies the quotient-of-a-simply-connected-space/deck-group theorem;
the missing RP² work is the concrete antipodal/projectivization adapter. The
latter is the closest existing polygon-surface program, but it currently
contains the pairing, quotient, open-cover, and boundary infrastructure rather
than the final genus-two van Kampen equivalence.

## Remaining lemmas

### `apm_t92J05_bridge_projectivePlane_fundamentalGroup` — LIBRARY

**Statement in words.** At every basepoint of the concrete real projective
plane, its fundamental group is multiplicatively equivalent to `ZMod 2`.

**Why true.** Identify the projectivization of `ℝ³` with the quotient of the
unit two-sphere by the free antipodal action of `Z/2`. Prove that this
identification is a homeomorphism and that the sphere quotient projection is
the corresponding two-sheeted covering. The sphere is simply connected by
the already imported sphere theorem. Then apply
`ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`
and transport the resulting equivalence through the homeomorphism and between
basepoints. The topology audit names precisely the two missing ingredients:
the antipodal/projectivization covering identification and its adapter to the
deck-group quotient theorem.

**Expected size.** LIBRARY, about 300–500 lines. The 2026-10-13 audit estimates
the antipodal cover construction at 100–180 lines, the generic/simple-cover
adapter at 80–140 lines, and the concrete final transport at 30–60 lines. The
generic deck-group quotient computation itself is already sorry-free.

**Dependencies.** Only the definitions block and the imported sorry-free
covering/deck-group and sphere-simple-connectivity modules. It is independent
of the genus-two computation.

**Truth check.** The antipodal action on `S²` is free because `u = -u` would
force `u = 0`, impossible on the radius-one sphere. Its acting group has two
elements. The standard hand computation therefore gives `π₁(RP²) = Z/2`.
Changing the basepoint cannot change the group because `RP²` is path connected.
This also agrees with the alternative CW presentation `⟨a | a²⟩`.

### `apm_t92J05_standard_genusTwo_fundamentalGroup` — LIBRARY

**Statement in words.** At every basepoint of the standard oriented
genus-two polygon surface, the fundamental group is the presented group on
four generators with relator `[a₁,b₁][a₂,b₂]`.

**Why true.** Use the polygon radial open cover developed in
`ConstructionTargets.PolygonSurfacePiOne`. The punctured polygon quotient
deformation-retracts onto its boundary graph, a wedge of four circles, while
the inner piece is contractible and their overlap represents the boundary
word. Seifert--van Kampen gives the quotient of `FreeGroup (Fin 4)` by the
normal closure of that single word, definitionally the `PresentedGroup` used
here. Transport from the polygon's distinguished point to an arbitrary `x`
using path connectedness. This is the same polygon-surface π₁ foundation as
the shared `ConstructionTargets/PolygonSurfacePiOne.lean` program; the theorem
is deliberately stated once rather than split into fake small lemmas.

**Expected size.** LIBRARY, about 600–1200 lines from the current banked
polygon infrastructure. The older topology audit estimated the final
genus-two specialization alone at 300–600 lines, but the absent general
van Kampen/open-cover descent can make the complete program larger.

**Dependencies.** Only the definitions block and the imported sorry-free
`Surfaces` and `PolygonSurfacePiOne` modules. It is independent of the RP²
computation.

**Truth check.** Cutting the standard surface along its four one-cells leaves
an octagon whose oriented boundary reads
`a₁ b₁ a₁⁻¹ b₁⁻¹ a₂ b₂ a₂⁻¹ b₂⁻¹`. Attaching the two-cell kills exactly this
word. Abelianizing kills both commutators and produces `Z⁴`, matching
`H₁(Σ₂; Z)`; at genus zero the analogous construction would have no
generators, and at genus one it reduces to the familiar commuting-pair torus
presentation. These endpoint checks support the indexing and orientation.

## Already proved assembly

`apm_t92J05_bridge_genusTwo_fundamentalGroup` is a short, sorry-free adapter:
it consumes the homeomorphism supplied by `apm_t92J05_IsGenusTwoSurface`,
applies the standard-model LIBRARY theorem at the image basepoint, and
transports fundamental groups along the homeomorphism. The extra compactness,
separation, path-connectedness, chart, and manifold assumptions are not needed
by this adapter because the explicit homeomorphism already contains the
classification conclusion.

The final theorem pairs the RP² result with the proved product calculation and
the proved genus-two adapter. It has no direct `sorry`.

## Dependency layers

- **Layer 1, parallel LIBRARY programs:**
  `apm_t92J05_bridge_projectivePlane_fundamentalGroup` and
  `apm_t92J05_standard_genusTwo_fundamentalGroup`.
- **Layer 2, already compiled:** the arbitrary-space genus-two transport and
  final conjunction assembly after the two Layer 1 conclusions are supplied.

Lemma count: **2 remaining lemmas**, both genuine LIBRARY boundaries and fully
independent of one another. There is no mathematical doubt about either
statement. The only uncertainty is engineering size, especially how much of
the general polygon van Kampen machinery the shared program still needs.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t92J05/Blueprint.lean
```

The final output of `#print axioms apm_t92j05` was:

```text
'apm_t92j05' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The only two `sorry` warnings are the two Layer 1 LIBRARY lemmas. The main
theorem and all transport/assembly declarations are sorry-free.

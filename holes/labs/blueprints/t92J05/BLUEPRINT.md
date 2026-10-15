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

### Projective-plane leaves (all parallel)

The old 300–500 line boundary is now a sorry-free assembly of these seven
top-level leaves. Dependencies are arguments, not references to other leaves,
so every seat can compile against the current file independently.

- `apm_t92J05_antipodalAction_free` (30–50 lines): the antipodal
  `Multiplicative (ZMod 2)` action is free. Use `fin_cases g`, subtype extensionality,
  `two_smul`, and `smul_eq_zero`. Radius one excludes the zero vector.
- `apm_t92J05_antipodalAction_properlyDiscontinuous` (40–80 lines): the action
  is properly discontinuous. Use finiteness/discreteness of `ZMod 2` and the
  Mathlib finite-group-action instance/constructor for
  `ProperlyDiscontinuousSMul`; alternatively separate `x` and `-x` by metric
  balls. Freeness is deliberately not a hypothesis, so this leaf is independent.
- `apm_t92J05_projectivePlane_homeomorph_antipodalQuotient` (100–150 lines):
  normalize each nonzero representative of `Projectivization ℝ (Fin 3 → ℝ)`
  to the unit sphere, prove that changing a real scalar changes the normalized
  vector only by sign, and descend in both directions. Use
  `Projectivization`, `projectivizationSetoid`, `Homeomorph.quotient`/quotient
  induction, `Real.norm_eq_abs`, and `abs_mul`. This is the largest leaf.
  The zero vector never represents a projective point; normalization therefore
  has no zero-denominator case.
- `apm_t92J05_antipodalQuotient_fundamentalGroup` (20–35 lines): given the
  free and properly-discontinuous conclusions explicitly, install the latter
  with `letI`, install sphere simple-connectivity using
  `ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected
  2 (by norm_num)`, and apply the exact theorem
  `ConstructionTargets.DeckGroupQuotientFundamentalGroup.freeProperlyDiscontinuousQuotient_fundamentalGroupEquiv`.
  The needed `T2Space`, `LocallyCompactSpace`, and `LocPathConnectedSpace`
  instances for the radius-one sphere should infer.
- `apm_t92J05_projectivePlane_fundamentalGroup_at_one_point` (20–35 lines):
  choose any sphere point (for example the first coordinate unit vector), use
  the supplied deck conclusion there, and transport with
  `ConstructionTargets.BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph`.
  Both the homeomorphism and deck result are explicit hypotheses.
- `apm_t92J05_projectivePlane_pathConnected` (40–70 lines): prove the concrete
  projectivization path connected, either from the quotient map from `S²`
  (using `isPathConnected_sphere` and continuous surjective image) or directly
  through normalized representatives. Dimension is three and radius is one,
  so the sphere theorem's rank inequality holds; the antipodal quotient removes
  the sphere's only sign ambiguity.
- `apm_t92J05_fundamentalGroup_all_basepoints` (10–20 lines): from an explicit
  `PathConnectedSpace X` value and one computed basepoint, use
  `FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`. This lemma is
  generic and handles the arbitrary-basepoint endpoint without hiding topology.

The action and continuity instances preceding the leaves are already proved.
The final `apm_t92J05_bridge_projectivePlane_fundamentalGroup` only installs
the action instance, feeds conclusions into the next adapters, and contains no
`sorry`. Empty-space vacuity is impossible because the one-point leaf exhibits
a basepoint; no boundary or dimension-zero case is present.

### Genus-two leaves

The former 600–1200 line boundary is now a sorry-free assembly from three
parallel leaves.  The generic theorem is deliberately useful beyond this
problem: it says that for path-connected open `U,V` covering `X`, with
path-connected overlap and simply connected `V`, the inclusion `π₁(U) →
π₁(X)` is onto and its kernel is the normal closure of the overlap image.
This is equivalent to the requested "attach one 2-cell" quotient statement;
it is slightly stronger because the overlap need not first be identified with
`ℤ`.

- `apm_t92J05_twoOpen_simplyConnectedRight_kernel` (**LIBRARY**, 100–150
  lines): extract surjectivity and the exact kernel from the two-open groupoid
  pseudopushout.  Start with
  `ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence`
  and its `pseudopushoutPostcomposeNatIso`; use
  `ConstructionTargets.TwoOpenLegCompatibleConnectorSystems.leftConnectors`
  and `rightConnectors` to pass to the chosen overlap basepoint.  Unlike
  `ConstructionTargets.TwoOpenFreeProductMapping.groupEquivalence`, this leaf
  must retain the non-simply-connected overlap; that existing theorem cannot
  be applied here.  Finish the kernel inclusions with
  `Subgroup.normalClosure_le_normal`, `Subgroup.subset_normalClosure`, and the
  pseudopushout universal property.  Independent of both leaves below.
- `apm_t92J05_quotient_normalClosure_equiv_of_kernel` (**LIBRARY, pure
  algebra**, 15–30 lines): use
  `QuotientGroup.quotientKerEquivOfSurjective f hsurj`, reverse it, and rewrite
  the quotient subgroup with `QuotientGroup.quotientMulEquivOfEq hker` (the
  same exact pattern is already compiled in
  `t93J03Closure.kleinPolygonFundamentalGroupEquivPresented_of_vanKampen`).
  Independent of all topology and valid for arbitrary groups, including the
  trivial group and a trivial overlap map.
- `apm_t92J05_genusTwo_polygon_attach_specialization` (**LIBRARY, 100–150
  lines): given the generic quotient theorem explicitly, instantiate it on
  `PolygonSurfacePiOne.openCover` for
  `PolygonSurfacePiOne.standardPairingData true 2`; install simple
  connectedness of the inner member from `openCover.contraction`, identify the
  annulus using `openCover.overlap_homeomorph`, retract the outer member using
  `PairingData.punctureDeformationRetract`, and use
  `PairingData.skeletonHomeomorphWedge`, then iterate
  `PointWedgeVanKampen.genericPointWedgeFundamentalGroupEquiv` and
  `PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum` for the free-group
  coordinates (compare the already compiled two-generator chain
  `t93J03Closure.kleinActualSkeletonFundamentalGroupEquivCoprod` and
  `circleFundamentalGroupCoprodEquivFreeGroupBool`).  The signed arc formula
  `PairingData.signedWedgeArc_pair` gives precisely
  `a₁ b₁ a₁⁻¹ b₁⁻¹ a₂ b₂ a₂⁻¹ b₂⁻¹`; use
  `Subgroup.map_normalClosure` and `PresentedGroup`'s quotient equivalence to
  identify the quotient.  This leaf is independent of the proof of the
  generic theorem because that conclusion is an explicit hypothesis.

`apm_t92J05_twoOpen_attach_one_cell` is the sorry-free generic assembly of the
first two leaves.  `apm_t92J05_genusTwo_polygon_vanKampen_at_center` is now the
sorry-free assembly of that generic theorem and the geometric specialization.
- `apm_t92J05_genusTwo_pathConnected` (20–40 lines): path connectedness of
  the concrete quotient. Use the continuous surjective disk quotient map and
  `IsPathConnected.image`, or the existing surface/path-connected instance if
  available. The disk is nonempty; genus `2` makes the polygon nondegenerate.
  Independent of the group calculation.
- `apm_t92J05_genusTwo_all_basepoints` (10–20 lines): given path-connectedness
  and the center calculation as explicit hypotheses, use
  `FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`, then compose with
  the supplied center equivalence. Independent and compilable before either
  input leaf lands.

`apm_t92J05_standard_genusTwo_fundamentalGroup` is now a sorry-free assembly.
The explicit center is represented by `0` in the closed disk, so it is never a
boundary-identification ambiguity. Cutting along the four one-cells gives the
oriented octagon word above. Abelianization is `Z⁴`, checking both the number
of generators and the commutator signs. Genus zero is intentionally outside
the concrete leaf; genus two has eight boundary arcs and four paired orbits.

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

- **Layer 1, parallel LIBRARY programs:** the seven projective-plane leaves
  above, and the independent `apm_t92J05_standard_genusTwo_fundamentalGroup`.
- **Layer 2, already compiled:** the arbitrary-space genus-two transport and
  final conjunction assembly after the two Layer 1 conclusions are supplied.

Lemma count: **10 remaining lemmas**: seven small projective-plane leaves and
the three independent genus-two/van-Kampen leaves above. There is no mathematical doubt
about their statements. The main uncertainty is the exact Mathlib quotient API
needed by the homeomorphism leaf, and engineering size for genus two.

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

## Note on the LIBRARY leaf (claude-14, 2026-10-14)
`genusTwo_polygon_vanKampen_at_center` is not starting from nothing. Already banked, sorry-free:
- the generic polygon data `PolygonSurfacePiOne.PairingData` (radial open cover, skeleton ≅ wedge)
- `TwoOpenFundamentalGroupoidPseudopushout`
- `PointWedgeVanKampen`
- the Klein instance in `t93J03Closure.lean`: inner contractible, overlap π1 ≅ ℤ, skeleton presentation map surjective, with its kernel computed

The missing step is generic: a pseudopushout with contractible inner open and overlap ≅ ℤ makes π1(space) the quotient of π1(skeleton) by the attaching word.  It is now isolated as `apm_t92J05_twoOpen_simplyConnectedRight_kernel` plus the pure-algebra quotient leaf above.  The same generic theorem can supply the `KleinPolygonBasedVanKampen` input in `t93J03Closure` and the degree-`d` disk attachments in `t99A01`.

# t02A01 blueprint

## Triage

Verdict: **true and faithful**.  The registered theorem is the covering-space
statement in `problem.md`, specialized to the explicit square-annulus quotient.
The hypotheses give an `n`-element group acting simply transitively on every
fiber.  The boundary loop of the punctured torus is a commutator, hence has
trivial image in the abelian deck group `ZMod n`; its restricted monodromy is
therefore trivial and each sheet gives a different boundary component.

Degenerate checks:

* `n = 0` is excluded by `hn : 0 < n`; this matters because `ZMod 0` is not the
  intended finite cyclic group.
* For `n = 1`, simple transitivity makes every fiber a singleton and the claim
  reduces to connectedness of the one lifted boundary circle.
* Empty total space is excluded by `hp_surjective`, since the concrete boundary
  (indeed the base) is nonempty.
* A disconnected total space is not an immediate counterexample: the stated
  simply transitive deck action can permute sheets/components, and the boundary
  component count is controlled by restricted monodromy rather than global
  connectedness of `Stilde`.

No solve-loop record, cached partial proof, topology worklist row, or audit for
`t02A01` was present in the specified locations.  I searched all sorry-free
`ConstructionTargets` modules with names/content involving `Cover`,
`Monodromy`, `Circle`, `PuncturedTorus`, and `FundamentalGroup`.  The closest
existing result is
`ConstructionTargets.CoveringMonodromyCosets`: it supplies `IsCoveringMap.monodromy`
in a useful form and proves the fiber/coset theorem for a path-connected total
space.  It does **not** provide the component-orbit theorem needed here, nor the
square-annulus boundary-commutator calculation.  The blueprint imports that
sorry-free module explicitly.

## Definitions

`Blueprint.lean` copies all definitions and the theorem signature verbatim from
`Main.lean`.  It additionally defines:

* `apm_t02a01_boundarySpace`, the subtype of points on the inner boundary;
* `apm_t02a01_restrictedCover`, the restriction of `p` over that subtype.

Neither definition encodes a desired conclusion.

## Lemmas

### Geometry leaves

1. `apm_t02a01_boundary_homeomorph_circle` — **LIBRARY**, 100–150 lines,
   independent.  Construct the centered-radius-`1/4` parametrization and prove
   that the quotient is injective there.  Useful APIs: `Homeomorph.SetCongr`,
   `Homeomorph.trans`, `IsQuotientMap`, `Quotient.eq`, and the norm/sphere
   homeomorphisms in `Mathlib.Topology.MetricSpace.Isometry`.  The missing hard
   point is the `Relation.EqvGen` normal form: inner points never participate in
   an outer-edge generator.  The extreme inner-circle points have coordinates
   `1/4` or `3/4`, never `0` or `1`; radius is positive, so the set is nonempty
   and not collapsed.  This is the one genuinely missing geometric foundation.

2. `apm_t02a01_boundary_pathConnected` — 20–40 lines, independent given its
   explicit homeomorphism hypothesis.  Use `Homeomorph.isPathConnected_image`
   (or transport a `PathConnectedSpace` instance) and the existing circle
   instance.  It cannot be vacuous: its conclusion is an instance on the
   boundary, while its hypothesis is only an equivalence of spaces.

3. `apm_t02a01_boundary_locPathConnected` — 20–40 lines, independent given
   its explicit homeomorphism hypothesis.  Use invariance of
   `LocPathConnectedSpace` under a homeomorphism and the circle instance.

`apm_t02a01_boundary_geometry` is now a sorry-free assembly of leaves 1–3.

### Restricted monodromy leaves

4. `apm_t02a01_restrictedCover_isCovering` — 30–70 lines, independent.  Pull
   each `IsEvenlyCovered` neighborhood back to the boundary subtype.  Relevant
   Mathlib objects are `IsCoveringMap`, `IsEvenlyCovered`,
   `LocalHomeomorph.restr`, `LocalHomeomorph.subtypeRestr`, and
   `IsCoveringMap.isLocalHomeomorph`; if available in the installed version,
   use the standard pullback/base-change lemma directly.  Empty boundary would
   still be harmless for this statement, and no surjectivity of `p` is needed.

5. `apm_t02a01_boundary_monodromy_is_deck_commutator` — **LIBRARY**, 100–150
   lines after leaf 1, otherwise independent because `hcov` and the simply
   transitive deck action are explicit.  It
   isolates exactly the polygon calculation: every lifted inner-boundary loop
   ends at `deck (u + v - u - v) e`.  Use
   `IsCoveringMap.liftPath`, `liftPath_trans`, `liftPath_lifts`,
   `liftPath_apply_one_eq_of_homotopicRel`, `monodromy_trans_apply`, and
   `Path.Homotopic.Quotient.mk_surjective`.  The required missing input is the
   square-annulus relation saying the inner boundary represents `[a,b]`; the
   nearby `ConstructionTargets.PolygonOuterRadialRelation.surfaceRel_boundary`
   and `PolygonSurfacePiOne` normal-form lemmas are the models, but do not
   directly cover this quotient.  This leaf deliberately returns endpoint
   equality, not trivial monodromy, so it does not silently include the
   abelian-group argument.  Reversing boundary orientation merely replaces the
   commutator by its inverse, also zero in `ZMod n`.

6. `apm_t02a01_deck_commutator_apply` — 10–25 lines, fully independent.  Use
   `sub_eq_add_neg`, `add_comm`, `add_left_neg`, `add_zero`, then
   `hdeck_zero`; `hdeck_add` is intentionally unnecessary because the polygon
   leaf already packages the endpoint as one deck-group element.  The identity
   also holds for `ZMod 0` and `ZMod 1`, so this helper has no positivity
   hypothesis.

`apm_t02a01_boundary_monodromy_trivial` is now a sorry-free assembly of leaves
4–6.  Its legacy `hdeck_add` and `hdeck_transitive` parameters remain only to
keep the registered interface byte-identical downstream.

### Component/fiber leaves

7. `apm_t02a01_component_meets_fiber` — 60–100 lines, independent.  Represent
   a connected component by a point, choose a base path in `B`, and lift it.
   Convert the lifted path to equality in `ConnectedComponents` using
   `ConnectedComponents.surjective_coe`, `ConnectedComponents.coe_eq_coe'`,
   `IsCoveringMap.liftPath`, `liftPath_zero`, and `liftPath_lifts`.  Reversing
   the chosen base path handles the endpoint convention.  Path connectedness
   rules out extra base components; the fiber is nonempty because it contains
   `e`.

8. `apm_t02a01_fiber_injective_on_components` — 90–150 lines, independent.
   Turn equality of connected components into a path between the fiber points;
   a covering over a locally path-connected base has locally path-connected
   total space, so connected components are path components.  Project that
   path to a based loop and identify its lifted endpoint using
   `hq.monodromy_map`, `hq.eq_liftPath_iff'`,
   `ConnectedComponents.coe_eq_coe`, and
   `connectedComponent_eq_pathComponent`.  Then apply `hmono`.  This statement
   contains the essential monodromy implication but not surjectivity or the
   equivalence construction.  For a product cover it says distinct sheet
   labels lie in distinct components.

`apm_t02a01_components_equiv_fiber` is now a six-line sorry-free assembly:
the map from the chosen fiber to connected components is bijective by leaves 7
and 8, and `Equiv.ofBijective` is reversed.

### 4. `apm_t02a01_fiber_card`

**Statement in words.** A fiber of the restricted cover has cardinality `n`
under the supplied simply transitive `ZMod n` deck action.

**Why true.** Send `z : ZMod n` to `deck z x`.  `hdeck_over` keeps this point in
the same restricted fiber.  Existence and uniqueness in `hdeck_transitive` give
surjectivity and injectivity, hence an equivalence with `ZMod n`; finish with
`Nat.card_zmod`.

**Estimate.** 30–50 lines.

**Dependencies.** None.

**Truth check.** At `n = 1`, the unique-action hypothesis forces the fiber to
be a singleton.  More generally, this is exactly the elementary torsor
cardinality argument and does not require `hcover`.

## Dependency layers

* Layer 1 (fully parallel): leaves 1, 4, 6, 7, 8, and
  `apm_t02a01_fiber_card`.
* Layer 1 as well, with explicit inputs supplied as hypotheses: leaves 2, 3,
  and 5.  Thus no leaf's proof needs another sorry-backed declaration.
* Layer 2 consists only of the three existing sorry-free assembly lemmas.
* Layer 3 is the unchanged main proof, which installs the geometry instances,
  chooses a boundary point, applies the monodromy/component assemblies, and
  rewrites by the already-proved fiber-cardinality lemma.

## Compilation and axiom gate

Command:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t02A01/Blueprint.lean
```

Output of `#print axioms apm_t02a01`:

```text
'apm_t02a01' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus `sorryAx` enters the main theorem only through the eight new leaf lemmas;
all three formerly coarse library lemmas and the main theorem are sorry-free.

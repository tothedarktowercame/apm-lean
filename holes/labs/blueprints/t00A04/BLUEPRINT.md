# Blueprint for t00A04

## Triage

Verdict: **true and registered faithful**.

The theorem is registered faithfully.  One subtle point is that it does not
carry `[I.Boundaryless]`: nevertheless here the model type and vector space are
both the same finite-dimensional `E`.  The model map `I : E → E` is a
continuous injection, so invariance of domain makes its range open; every
manifold point is therefore an interior point.  The interval is not a
counterexample: Mathlib's interval instance uses
`modelWithCornersEuclideanHalfSpace 1`, whose model type is
`EuclideanHalfSpace 1`, so it cannot instantiate an `I : ModelWithCorners ℝ E E`.

I tested the dangerous degeneracies.  A one-point zero-manifold would be a
counterexample to the raw source, but `Nontrivial X` excludes it.  A nontrivial
compact zero-manifold is disconnected, so its identity cannot be homotopic to
a constant.  In positive dimension, compactness and absence of boundary rule
out a contraction (equivalently, top homology with mod-2 coefficients is
nonzero).  The interval is not a counterexample because it is a manifold with
boundary, not an `IsManifold I ∞` space in Mathlib's boundaryless sense.

The solve-loop's already proved retraction argument was reused.  The topology
worklist shows that the broad compact-support/local-homology route stalled at
a relative Mayer--Vietoris theorem; none of its unfinished modules is imported.
A search through every sorry-free `ConstructionTargets/*.lean` file found
specialized noncontractibility results (notably
`CircleNoncontractible.circle_not_contractible`) but no theorem for arbitrary
compact manifolds.

## Lemmas

### `t00A04_model_subsingleton_of_finrank_zero`

**Statement.** A finite-dimensional real normed space of finrank zero is a
subsingleton.

**Proof route / Mathlib tools.** Use `Module.finrank_zero_iff` (or
`FiniteDimensional.finrank_eq_zero`) to get that every vector is zero, then
`subsingleton_iff`.  If the exact iff is awkward, apply
`FiniteDimensional.finrank_eq_zero_iff` and the standard `Subsingleton` instance
for a zero module.

**Expected size.** 10--30 lines.  **Independent:** yes.

**Truth check.** The scalar field is `ℝ`, hence nontrivial; the result would
need care over the zero ring, but that degeneracy is absent here.

### `t00A04_manifold_discrete_of_model_subsingleton`

**Statement.** A manifold modelled on a subsingleton normed space is discrete.

**Proof route / Mathlib tools.** For each `x`, use
`isOpen_range_chartAt`/`ChartedSpace.chartAt`, the chart source neighbourhood,
and injectivity of `chartAt I x` on its source.  Since the target is a
subsingleton, every point in the source equals `x`; hence `{x}` is a
neighbourhood and is open.  Finish with `discreteTopology_iff_isOpen_singleton`
(search nearby declarations if the spelling differs).

**Expected size.** 40--90 lines.  **Independent:** yes; `Subsingleton E` is an
explicit instance rather than a dependency on the finrank lemma.

**Truth check.** Charts have open source containing their centre, so no
connectedness or nonemptiness assumption is hidden.  The empty `X` case is
also discrete.

### `t00A04_discrete_nullhomotopic_identity_subsingleton`

**Statement.** If the identity of a discrete space admits the blueprint's
real-parameter null-homotopy, the space is a subsingleton.

**Proof route / Mathlib tools.** For fixed `x`, compose the homotopy with
`Continuous.continuousAt` or use `ContinuousMap`; the map `t ↦ H (x,t)` is
continuous.  Its image of connected `Set.univ : Set ℝ` is connected via
`IsConnected.image`, and a connected subset of a discrete space is a
subsingleton (`IsConnected.subsingleton` / `isPreconnected_iff_subsingleton`
in a discrete topology).  Compare its values at `0` and `1`, then rewrite with
the endpoint hypotheses.  Repeat for arbitrary `x` to show all points equal to
the chosen constant.

**Expected size.** 35--80 lines.  **Independent:** yes.

**Truth check.** The homotopy parameter is all of `ℝ`, not `I`; `ℝ` is
connected and both endpoints lie in it.  For empty `X`, `Subsingleton X` is
valid and the existential null-homotopy is in fact impossible if `X` is empty
and the codomain is also `X`.

### `t00A04_nontrivial_not_subsingleton`

**Statement.** A `Nontrivial` type cannot be a `Subsingleton`.

**Proof route / Mathlib tools.** `not_subsingleton_iff_nontrivial` (or obtain
`⟨x,y,hxy⟩` from `exists_pair_ne X` and contradict `Subsingleton.elim x y`).

**Expected size.** 5--15 lines.  **Independent:** yes.

**Truth check.** This is exactly the typeclass meaning of `Nontrivial`.

### `t00A04_ModTwoHomology`

An abbreviation for coefficient singular homology using `ModuleCat.{u}
(ZMod 2)` and coefficient module `ULift.{u} (ZMod 2)`.  The lift is essential:
the registered theorem is universe-polymorphic, whereas the existing
homotopy-invariance helper's simplest examples use `X : Type`.

### `t00A04_boundarylessManifold_of_finiteDimensional_selfModel` — LIBRARY

**Statement.** For `I : ModelWithCorners ℝ E E` with finite-dimensional `E`,
every `I`-manifold is a `BoundarylessManifold I X`.

**Route.** Apply finite-dimensional invariance of domain to the continuous
injective model map `I : E → E`, proving `range I` open.  Extended charts then
map every point into `interior (range I)`, which is exactly
`ModelWithCorners.IsInteriorPoint`; use `BoundarylessManifold.mk`.

**Size.** LIBRARY, 100--250 lines. **Independent:** yes.

**Truth check.** The closed interval does not satisfy the self-model premise:
its model type is `EuclideanHalfSpace 1`.  Open balls and proper open convex
ranges do satisfy the conclusion even though `I.Boundaryless` (range equals
all of `E`) need not hold.

### `t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial` — LIBRARY (universe bridge)

**Statement.** Given the Type-0 theorem (`hType`: every nonempty compact
Hausdorff boundaryless manifold `X₀ : Type` over `E₀ : Type` has nontrivial
`H_(finrank E₀)(X₀; ZMod 2)`), the same holds for `X : Type u` over `E : Type*`.

**Size.** LIBRARY, 80--160 lines. **Independent:** yes; the Type-0 result is
the hypothesis `hType`, supplied in the assembly by
`..._nontrivial_Type`.  Proof: `X` is `Small.{0}` (finitely many charts into
`E`, so cardinality at most the continuum); move it to a homeomorphic
`X₀ : Type` with charts into `EuclideanSpace ℝ (Fin (finrank E))`, apply
`hType`, and transfer nontriviality of `H_d` with `ULift` coefficients along
the homeomorphism.

**Truth check.** `S¹`, `RP²`, and the Klein bottle all have nonzero mod-2 top
homology; the latter two explain the coefficient choice.  `[0,1]` fails the
explicit `BoundarylessManifold` hypothesis.  At dimension zero the claim is
also true for a nonempty compact zero-manifold (`H₀ ≠ 0`).  For `X` already in
`Type` and `E` in `Type`, the bridge is `hType` up to the `ULift` coefficient
identification.

### `t00A04_compact_boundaryless_manifold_top_modTwo_homology_nontrivial_Type` (assembly, proved)

Sorry-free assembly of the Hatcher leaves below: F1 → F2e → F3e → chart
transport → F3 at `A = univ` → F4.

### `t00A04_HatcherConclusion`

The actual 3.27 package for compact `A`: vanishing of `H_i(X,X\A;F₂)` above
`d`, an everywhere locally nonzero degree-`d` class, and point restrictions
detecting zero.  `t00A04_modTwo_pointRestriction` is the homology map of
`CoefficientRadialPair.pairMap` for `Aᶜ ⊆ {x}ᶜ`.

### `t00A04_hatcherConclusion_compact_convex_euclidean` — LIBRARY F1

Compact convex `A ⊆ EuclideanSpace ℝ (Fin d)` satisfies the package.
Estimated 120--200 lines; independent.  Check `A={x}` against model local
homology and a closed ball by radial deformation/excision.

### `t00A04_hatcherConclusion_union` — LIBRARY F2

The packages for compact `A`, `B`, and `A∩B` imply the package for `A∪B`.
It additionally assumes every point-local top group has at most one nonzero
element.  Estimated 120--220 lines; independent.  Use
`CoefficientCompactComplementTransportedExactness` at `ZMod 2`.  On the open
tripod the new local-uniqueness hypothesis fails at the branch point, exactly
excluding the counterexample.  For `A=B` it reduces to identity data; for
`A∩B=∅`, the empty-intersection term gives the disjoint-union case.

### Euclidean and manifold induction leaves

`t00A04_modTwoLocalHomology_unique_nonzero` is the separate chart-excision
leaf giving the missing F2 hypothesis.  `..._finite_union_convex_euclidean`
(F2e, 60--120 lines) inducts on a `Finset`; intersections remain convex.  Test
cases are disjoint and overlapping closed balls.

`..._compact_euclidean` (F3e, LIBRARY, 150--300 lines) is Hatcher's relative
cycle/support argument extending finite convex unions to arbitrary compact
sets.  For a circle in `ℝ²`, `H₂(ℝ²| S¹)=F₂`; the additional `H₁=F₂`
is below dimension and is not constrained.

`..._compact_in_chart` transports the arbitrary-compact Euclidean result, not
just the convex case.  `..._compact_manifold` (F3, 100--180 lines) then uses a
finite chart cover: the induction intersection is an arbitrary compact subset
of the newest chart and is covered by the chart leaf.  For `S¹` covered by two
arcs, the intersection can be two disjoint arcs and is still handled.

### `t00A04_top_homology_nontrivial_of_hatcherConclusion_univ` — LIBRARY F4

At `A=univ`, identify `H_d(X,X\A;F₂)=H_d(X,∅;F₂)` with absolute
homology and use the everywhere-nonzero class at a point of nonempty `X`.
Estimated 40--90 lines; independent.  It yields the expected nonzero classes
for `S¹`, `RP²`, and the Klein bottle.

**Library context for the F leaves.** Hatcher 3.27/3.26
requires genuine relative Mayer--Vietoris and a finite-chart induction.
`ConstructionTargets.ProductionOpenCoverMayerVietoris` is for absolute
integral homology, not the needed relative `ZMod 2` sequence.
`ConstructionTargets.LocalHomologyNeighborhoodExcision.neighborhoodInclusion_Hsucc_isIso`
does give positive-degree local excision, but not the global patching theorem.
`ConstructionTargets.ManifoldFundamentalClass` is mostly integral, specialized
to Euclidean chart models and its completed global-generator material is
dimension one; it does not supply this arbitrary-dimensional mod-2 theorem.
The 5000-line t00A01 localization chain assumes/proves integral dimension-three
data and cannot be reused as a mod-2 compact-manifold fundamental class.

The F leaves above realize Hatcher's split: (1) compact convex chart sets, including point sets; (2)
coefficient-`ZMod 2` relative Mayer--Vietoris for unions; (3) positive-degree
chart excision; (4) finite-union and finite-chart induction; (5) evaluate at
`A = X`, where the constant local section `1` is nonzero.  At `A = {x}`, the
local group is the standard punctured-vector-space group; at `A = X`, the
complement is empty.  The declarations now use the reviewed coefficient
compact-complement, excision, and relative-pair APIs directly.

### `t00A04_identity_not_nullhomotopic_of_modTwoHomology_nontrivial`

**Statement.** If `n ≠ 0` and `H_n(X; ZMod 2)` is nontrivial, then
`ContinuousMap.id X` is not nullhomotopic.

**Route.** Use
`ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_zero_of_nullhomotopic`;
functoriality changes the identity's induced map to the identity morphism.
If that morphism is zero, evaluation shows every two homology classes equal,
contradicting `Nontrivial`.

**Size.** 30--70 lines. **Independent:** yes.  The current leaf is isolated
with one `sorry` because elaborating the universe-polymorphic categorical
proof exceeded six million heartbeats; its mathematical content is small.

**Truth check.** For contractible `X`, positive homology is zero, so the
`Nontrivial` hypothesis fails; the lemma does not incorrectly conclude that a
contractible identity is non-nullhomotopic.

### `t00A04_nullhomotopic_to_continuousMap`

**Statement.** A null-homotopy in the problem's all-real parameter convention
restricts to Mathlib's unit-interval `ContinuousMap.Nullhomotopic` convention.

**Proof route / Mathlib tools.** Define the standard homotopy by
`(t,x) ↦ H (x,t)` for `t : Set.Icc 0 1`; continuity is
`hH.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))`.
The endpoint fields are the two hypotheses after `simpa`.

**Expected size.** 15--30 lines. **Independent:** yes.

**Truth check.** Restriction is valid because the given homotopy is continuous
on every real time, hence in particular on `[0,1]`; no extension theorem or
boundary assumption is used.

### `t00A04_positive_dimensional_manifold_identity_not_nullhomotopic` (assembly, proved)

Installs `BoundarylessManifold` from the invariance-of-domain leaf, installs
nontrivial top homology from the fundamental-class leaf, converts the supplied
homotopy, and applies the generic homology endgame.  It contains no `sorry`.

### `t00A04_manifold_identity_not_nullhomotopic` (assembly, proved)

Splits `Module.finrank ℝ E` with `Nat.eq_zero_or_pos`.  The zero branch installs
the explicit `Subsingleton E` and `DiscreteTopology X` instances and combines
the three small topology leaves with `Nontrivial X`; the positive branch calls
the sole remaining LIBRARY leaf.  It contains no `sorry` itself.

### `t00A04_retract_inclusion_not_nullhomotopic` (already proved)

**Statement in words.** If `r ∘ ι = id` and `r` is continuous, then
non-null-homotopy of the identity implies non-null-homotopy of `ι`.

**Why true.** Postcompose a purported homotopy from `ι` to a constant with
`r`.  Its time-zero endpoint becomes `r (ι x) = x`, and its time-one endpoint
is the constant `r y`.

**Expected size.** Already proved, 15 lines.

**Dependencies.** Its assumption is exactly the conclusion of the LIBRARY
lemma, so a seat can prove the library theorem independently.

**Truth check.** Direct endpoint computation.  No continuity of `ι` is needed;
only continuity of `r` is used when postcomposing the homotopy.

## Dependency layers

* **Layer 1, all independent:** the four zero-dimensional leaves, the
  real-to-unit-interval conversion, invariance-of-domain, the boundaryless
  fundamental class, and the generic homology endgame.  The middle two are
  LIBRARY; the endgame is small.
* **Layer 2:** the positive-dimensional assembly, then
  `t00A04_manifold_identity_not_nullhomotopic` (both sorry-free).
* **Layer 3 (already proved):** the retraction lemma and `apm_t00a04`.

## Compilation and axioms

Compiled with:

```text
systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/t00A04/Blueprint.lean
```

The final compiler output was:

```text
holes/labs/blueprints/t00A04/Blueprint.lean:88:8: warning: declaration uses `sorry`
holes/labs/blueprints/t00A04/Blueprint.lean:97:8: warning: declaration uses `sorry`
holes/labs/blueprints/t00A04/Blueprint.lean:122:8: warning: declaration uses `sorry`
'apm_t00a04' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The warnings are exactly the invariance-of-domain leaf, the fundamental-class
leaf, and the small generic endgame leaf.  Both manifold assemblies, the
retraction lemma, and the main theorem contain no direct `sorry`.

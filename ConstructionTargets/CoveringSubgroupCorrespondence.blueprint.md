# Blueprint: covering spaces from fundamental-group subgroups

## Provenance and fixed representation

This blueprint follows the audits `t94J04` step
`surface_subgroup_connected_cover` and `t96A01` step
`finiteIndexSubgroup_covering`.  It also supplies the existence/coset part of
the routes for `t99J01`, `t97A03`, `t00A02`, and `t93J03`.

Mathlib supplies `IsCoveringMap.liftPath`, `liftHomotopyRel`, `monodromy`,
`monodromy_bijective`, `injective_path_homotopic_map`, and
`existsUnique_continuousMap_lifts_of_range_le`.  The repository supplies
`CoveringMonodromyCosets`, `CoveringLiftRestriction`,
`CoveringPathComponentDomain`, `DeckGroupQuotientFundamentalGroup`, and
`LiteralCoveringPullback`.  None constructs a covering from a subgroup.

We use the classical based-path construction.  A point of the total space is
an equivalence class of paths starting at `x`; two paths are equivalent when
their endpoints agree and their concatenation with the reverse path represents
an element of `H`.  The fibre uses a custom setoid whose relation is written
verbatim as `g * h⁻¹ ∈ H`; left/right coset terminology is not part of the
interface.  No normality or deck action is assumed.

### B1. Semilocally simply connected predicate

lean: `SemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop`,
defined by: for every `y`, some `U ∈ 𝒩 y` has every loop at `y` whose
range lies in `U` equal to the constant loop in `Path.Homotopic.Quotient y y`.

uses: Mathlib `Path.Homotopic.Quotient`

status: planned

## Implemented leaf boundary (2026-10-18)

The Lean interface is in `CoveringSubgroupCorrespondence.lean`.  The earlier
B1--B13 discussion remains the proof plan for the construction leaf; the
actual parallel seat boundary is:

- `exists_connected_subgroup_cover` (**LIBRARY**, 120--150 lines): B2--B10,
  the based-path construction, covering charts, connectedness, induced range,
  fundamental-group equivalence, and the distinguished-fibre coset
  equivalence.  Use `IsCoveringMapOn.of_openPartialHomeomorph`, path lifting,
  `injective_path_homotopic_map`, and `MulEquiv.ofBijective`.
- `exists_connected_subgroup_cover_of_small` (40--80 lines, uses the
  construction leaf as a black box): with `[Small.{v} X]`, realise the cover
  with total space in `Type v` by applying the construction to `Shrink X`
  (transported topology) and composing with the homeomorphism.  Added in
  review (claude-14, 2026-10-18): the first draft stated the construction with
  `∃ E : Type*`, an independent universe, which is false for `E : Type 0` over
  a base in `Type 1` too large for `Type 0` (a covering of a connected base by
  a nonempty space is surjective).  The construction leaf now produces
  `E : Type u` for `X : Type u`; t96A01 (`S : Type*`, `E : Type`) gets the
  smallness from `t96A01_surface_small`, t00J06 (`S : Type`, `X : Type*`)
  from `Small.{0} S`.
- `natCard_cosetQuotient` (40--70 lines, independent): compare the explicit
  relation with `QuotientGroup.rightRel`, use inversion and
  `Subgroup.index_eq_card`.
- `cosetQuotient_infinite_of_index_zero` (20--40 lines, independent): use the
  preceding index/card comparison argument directly with `Nat.card_eq_zero`;
  it deliberately takes no sibling theorem as an axiom.
- `covering_fiber_equiv` (20--40 lines, independent): choose a path and use
  `IsCoveringMap.monodromy_bijective`.
- `every_fiber_infinite_of_coset_equiv` (30--50 lines, parallel): the coset
  equivalence and index-zero fact are explicit hypotheses/data; combine them
  with monodromy.  It does not invoke either sibling sorry theorem.
- `exists_continuousMap_lift_of_range_le` (10--25 lines, independent): apply
  `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` and unpack
  `p ∘ lift = f`.

`connectedCover` is a sorry-free assembly from the construction witness and
`natCard_cosetQuotient`.  Consumer lifting is a sorry-free assembly using the
range equality stored in the same witness.

Truth checks: for `H = ⊤` the relation has one class and the construction is
the one-sheet/identity cover up to based covering equivalence.  For `H = ⊥`
it is the universal based cover.  Mathlib's `H.index = 0` is the infinite
index convention, so the explicit coset quotient and hence every fibre are
infinite.  No normality is assumed: the relation is literally
`g * h⁻¹ ∈ H`.  Path-connectedness of the base is used both to represent all
points by based paths and to transport fibres by monodromy.

The formulation is basepoint-local and does not mention simple connectivity
of `U`; this is exactly what the chart proof uses.

### B2. Good path-connected neighbourhoods

lean: `SemilocallySimplyConnected.good_nhds` : each `y` has an open,
path-connected neighbourhood `U` such that every loop in `U` maps trivially
to `FundamentalGroup X y`.

uses: B1, `LocPathConnectedSpace X`

status: planned

Refine the B1 neighbourhood to an open path-connected neighbourhood.  Local
path connectedness is used here and nowhere silently substituted by local
connectedness.

### B3. Based-path relation

lean: `subgroupCosetSetoid (H : Subgroup G) : Setoid G`, with
`subgroupCosetSetoid H g h ↔ g * h⁻¹ ∈ H`; and
`subgroupPathSetoid (x : X) (H : Subgroup (FundamentalGroup X x)) :
Setoid {y : X // Path x y}`

uses: Mathlib path concatenation, reversal, and homotopy quotient laws

status: planned

Relate `⟨y,α⟩` and `⟨z,β⟩` iff `y=z` and the based loop obtained from
`α.trans β.symm` (after transporting the endpoint equality) belongs to `H`.
Reflexivity uses `H.one_mem`; symmetry uses `H.inv_mem`; transitivity uses
`H.mul_mem`.  With loop classes `g=[α]` and `h=[β]`, this is definitionally
`subgroupCosetSetoid H g h`.  Thus B3 and B10 use literally the same relation,
including for nonnormal `H`.

### B4. Total space, projection, and basepoint

lean: `SubgroupCover x H`, `subgroupCoverMap : SubgroupCover x H → X`, and
`subgroupCoverBase : SubgroupCover x H`

uses: B3, `PathConnectedSpace X`

status: planned

The total space is the quotient by B3.  Projection takes a path class to its
endpoint and the basepoint is the constant path.  Path connectedness of `X`
is used to choose a based path ending at every base point, hence later to show
surjectivity and to describe every chart sheet.

### B5. Local sheet coordinates

lean: `subgroupCoverSheetEquiv` : over each good neighbourhood `U` from B2,
the preimage of `U` is equivalent to `U × F`, where `F` is the fibre over its
chosen centre.

uses: B2, B3, B4

status: planned

Choose paths inside `U` from its centre to each point and append them to a
representative path.  B2 proves independence of the internal path choice;
B3 proves independence of the representative.  The inverse truncates the
local segment.  The sheet label is a class of `subgroupCosetSetoid H`.  Prove
the two inverse equations before introducing topology.

### B6. Quotient topology and covering charts

lean: `subgroupCover_isCoveringMap : IsCoveringMap (subgroupCoverMap x H)`

uses: B2, B5, Mathlib `IsCoveringMapOn.of_openPartialHomeomorph`

status: planned

Give `SubgroupCover x H` the topology generated by the B5 sheet charts.
Each sheet coordinate is a homeomorphism onto an open copy of `U`; distinct
fibre coordinates give disjoint sheets, and their union is the full preimage.
This is the only node using semilocal simple connectivity.

### B7. Connectedness of the total space

lean: `subgroupCover_pathConnected : PathConnectedSpace (SubgroupCover x H)`

uses: B4, B6

status: planned

A class represented by `α` is joined to the constant-path class by the path
of initial segments of `α`.  Continuity is checked in B6 charts.

### B8. Image of the induced fundamental-group map

lean: `subgroupCover_fundamentalGroup_range` : the injective map induced by
`subgroupCoverMap x H` has range exactly `H`.

uses: B3, B6, Mathlib `injective_path_homotopic_map`, path lifting

status: planned

A base loop lifts to a loop at `subgroupCoverBase` exactly when its class is
in `H`, directly by B3: the endpoint class of `g` equals the class of `1`
iff `g * 1⁻¹ ∈ H`.  Covering homotopy lifting gives injectivity.  This
argument does not commute a loop class past `H`.

### B9. Fundamental group equivalence

lean: `subgroupCover_fundamentalGroupEquiv :
Nonempty (FundamentalGroup (SubgroupCover x H) (subgroupCoverBase x H) ≃* H)`

uses: B8

status: planned

Corestrict the induced homomorphism to `H`; B8 supplies bijectivity, then use
`MulEquiv.ofBijective`.

### B10. Fibre-coset equivalence

lean: `subgroupCover_fiberEquivCosets :
(subgroupCoverMap x H ⁻¹' {x}) ≃
  Quotient (subgroupCosetSetoid H)`

uses: B3, B4

status: planned

Send a loop class `g` in the fibre to `Quotient.mk (subgroupCosetSetoid H) g`.
B3 uses that identical setoid, so well-definedness, injectivity, and
surjectivity are direct.  No library quotient convention or normality
assumption occurs in this node.

### B11. Finite fibre cardinality

lean: `subgroupCover_fiber_card [H.FiniteIndex] :
Nat.card (subgroupCoverMap x H ⁻¹' {x}) = H.index`

uses: B10, `QuotientGroup.quotientRightRelEquivQuotientLeftRel`,
`Subgroup.index_eq_card`

status: planned

First identify `subgroupCosetSetoid H` with Mathlib's `rightRel H`: its
criterion `h*g⁻¹ ∈ H` differs from ours by inversion, and `H.inv_mem`
proves equivalence.  Then use Mathlib's inversion equivalence from `rightRel`
to the standard `leftRel` quotient, transport `Nat.card`, and apply
`Subgroup.index_eq_card`.  `FiniteIndex` is used only here.

### B12. Connected finite-index cover

lean: `connectedCover {X : Type*} [TopologicalSpace X]
[PathConnectedSpace X] [LocPathConnectedSpace X]
(hsl : SemilocallySimplyConnected X) (x : X)
(H : Subgroup (FundamentalGroup X x)) [H.FiniteIndex] :
∃ (E : Type*) (_ : TopologicalSpace E) (p : E → X) (e : E),
IsCoveringMap p ∧ PathConnectedSpace E ∧ p e = x ∧
Nat.card (p ⁻¹' {x}) = H.index ∧
Nonempty (FundamentalGroup E e ≃* H)`

uses: B4, B6, B7, B9, B11

status: planned

Take the explicit path-class cover with its `subgroupCosetSetoid H` fibre.  Path
connectedness constructs the classes and proves connectedness; local path
connectedness and `hsl` produce
the charts; finite index counts the fibre.  Thus every final hypothesis is
used by a named node.

### B13. Consumer specialisations

lean: declarations chosen in the consumer rows

uses: B12 plus each consumer's local/semilocal simple-connectivity proof

status: planned

Closed surfaces use manifold charts; the three-circle wedge uses its finite
graph neighbourhoods; finite free-action quotients may use B12 after their
fundamental group is known.  These are bounded adapters because their proofs
of `SemilocallySimplyConnected` use different representations.

## Split of `exists_connected_subgroup_cover` (claude-14, 2026-10-18)

lemma-1 returned PARTIAL with `_aux_good_nhds` proved (now banked in the
blueprint).  The cover is now explicit: `BasedPaths x = Σ y, [x ⇝ y]` with
`π₁` acting by `g • a = [g⁻¹] · a`, topology generated by the
path-neighbourhoods `basedPathNbhd U a` over all open `U` (the good `U` form a
basis of the same topology), `BasedCover H` = orbit space of `H` with the
quotient topology, `proj` = endpoint.  The main theorem is a sorry-free
assembly of six leaves, all parallel (dependents take `hp`/`hlift` as
hypotheses):

- `_aux_isCoveringMap` (LIBRARY-borderline, 80-120): charts over good `U`.
- `_aux_path_lift` (40-70): truncation path `t ↦ [γ|[0,t]]`, continuous in the
  generated topology, composed with the quotient map.
- `_aux_fiber` (30-50, algebra): fibre over `x` = left cosets `aH`; equinumerous
  with `subgroupCosetSetoid` classes (right cosets) via inversion.
- `_aux_mulEquiv_range` (15-30, generic): `injective_path_homotopic_map`, then
  `MulEquiv.ofBijective` onto the range.
- `_aux_range` (40-70): loop lifts to the truncation path (uniqueness of
  lifts), ending at `[⟨x, [γ]⟩]`, which is the basepoint iff `[γ] ∈ H`.
- `_aux_pathConnected` (10-20): every point is `mk ⟨y, [γ]⟩`; use `hlift`.

Truth checks: `.1` is continuous (preimage of open `U` is the union of
`basedPathNbhd U b` over `b.1 ∈ U`); continuity of the truncation at `t₀` only
needs `γ` near `t₀` inside `U`, and membership in a generating set
`basedPathNbhd U a` is preserved by extending inside `U`.

# t97A01 blueprint (revised 2026-10-15)

Previous version (two LIBRARY leaves, 10-13 review) moved to `old-2026-10-15/`.

## Verdict

Statement true and faithful (unchanged from the 10-13 review). `Blueprint.lean`
is the current `problems/t97A01/lean/Main.lean` verbatim (definitions,
proved helpers, frozen theorem) plus a blueprint section inserted between
`apm_t97a01_relator` and `apm_t97a01`, and an assembly proof replacing the
final `sorry`.

## State at revision

- **L1 (homology): DONE in Main.** `apm_t97a01_polygon_singular_homology` is
  sorry-free. Both frozen quotients are homeomorphic to `PairingData` spaces
  (`aabbccPairingData = nonorientableStandardPairingData 3`,
  `torusRP2PairingData`). `PolygonSurfaceHomology.polygonQuotient_homology`
  applies, and the Smith reductions live in `ConstructionTargets/t97A01Closure`.
- **π₁ transport to the pairing space: DONE in Main**
  (`apm_t97a01_TorusRP2_fundamentalGroupEquivPairingSpace`, base ↦ `center`).
- **Remaining: π₁ of `torusRP2PairingData.Space` at its centre.**
  `t97A01Closure` attacks this by hand-rolled based van Kampen (the
  `TorusRP2PairingSpaceBasedVanKampen` interface plus a large subdivision
  development, still open). This blueprint replaces that with the
  `AttachTwoCell` route.

## Route (π₁)

1. Generic: `polygonCellHomeomorph P : P.Space ≃ₜ Cell (polygonBoundaryWedgeLoop P)`
   for any `PairingData P`. The maps are written out: the disk becomes the 2-cell, and
   the wedge maps back through `P.skeletonHomeomorphWedge.symm`. Continuity, the
   cell-relation descent and `left_inv` are proved. Two leaves remain (G1, G2).
2. `cell_bword_piOne` (sorry-free): `AttachTwoCell.cell_piOne` and `cell_facts`.
   `π₁(wedge) → π₁(cell)` is onto, with kernel `normalClosure {wordClass P}`.
3. `legEquiv P : FreeGroup (PairingOrbit P.pair) ≃* π₁(wedge, orbitWedgeBase P)`.
   Surjectivity is banked (`finiteWedgeLegFreeGroupMap_surjective`).
   Injectivity reduces, without `sorry`, through `finiteWedgeOrbitFreeGroupMapComparison`
   to leaf G3 on `Fin (n+1)`.
4. `polygon_piOne_presentation` (generic, sorry-free): for any `M : F ≃* FreeGroup orbits`
   and a relator `r` with `normalClosure{legEquiv (M r)} = normalClosure{wordClass P}`,
   `π₁(P.Space, center) ≃* F ⧸ normalClosure{r}`.
5. Specialisation: `M = torusRP2BoundaryBasisEquiv.trans torusRP2OrbitFreeGroupEquiv.symm`.
   Leaf W transports the banked `torusRP2AttachingWord` (skeleton coordinates) to the wedge.
6. `apm_t97a01`: homology from Main, then the Main π₁ transport composed with step 5
   (`PresentedGroup` is definitionally `FreeGroup ⧸ normalClosure`).

## Leaves (all `sorry`; everything else is sorry-free)

| leaf | statement | generic? | est. size |
|---|---|---|---|
| G1 `polyToCell_respects` | `EqvGen P.Rel x y → cellDisk γ x = cellDisk γ y` | generic | ~40 lines (copy t97J04 `X_fwd_aux_edges`, 8 ↦ `P.edgeCount`) |
| G2 `cellDisk_surjective` | the 2-cell's characteristic map is onto | generic | ~45 lines (copy t97J04 `Xc_points_aux_word_surjective` and `Xc_points`) |
| G3 `finiteWedgeFinLegFreeGroupMap_injective n` | positive-leg map `FreeGroup (Fin (n+1)) → π₁(wedge)` injective | generic | 80–120 lines (`finiteWedge_finSucc_fundamentalGroup_free`, `circlePositiveFundamentalClass = gen^{±1}`) |
| W `torusRP2_boundary_word` | frozen relator in leg coords normally generates the boundary word class | specific | ~60 lines (map `torusRP2AttachingWord` through `torusRP2SkeletonFundamentalGroupEquivWedge`) |

All four are independent and can run in parallel. G1, G2 and G3 produce reusable library
results: the polygon ≅ cell homeomorphism, and the wedge π₁ being free in leg coordinates.
Once they land, `polygon_piOne_presentation` gives π₁ of every one-vertex polygon surface
from just a boundary-word lemma like W. These are candidates to move into `ConstructionTargets`.

## Checks

- Compiled: `flock … lake env lean holes/labs/blueprints/t97A01/Blueprint.lean` has 0 errors.
  It gives exactly 4 `declaration uses sorry` warnings, at lines 416, 474, 507 and 633,
  which are the four leaves.
- `#print axioms apm_t97a01` gives `[propext, sorryAx, Classical.choice, Quot.sound]`.
  `sorryAx` comes only through the leaves. The homology helper and the π₁ transport print
  without `sorryAx`.
- The frozen theorem statement and the whole Main prefix (from `open CategoryTheory` to
  the theorem) are byte-identical, checked by script.
- Built the missing oleans with `lake build ConstructionTargets.t97A01Closure`. This also
  built `KleinPlaneActionFree`, `t93J03Closure` and `T97A01SmithQuotients`.
- Truth: G1 and G2 are the generic forms of proved t97J04 lemmas. G3 is the standard
  freeness of a wedge of circles. W is the banked `torusRP2AttachingWord` written in
  different coordinates. I checked by hand that `legEquiv (M r) = legMap (orbitEquiv.symm
  (basis r))` and that `SkelFin = EquivWedge.symm ∘ legMap ∘ orbitEquiv.symm`.

## Risks

- `ConstructionTargets/t97A01Closure.lean` is under active edit (subdivision van Kampen,
  commits to 18:00 today). W relies on its stable early part (lines ≤ 1000:
  `torusRP2AttachingWord`, `torusRP2BoundaryBasisEquiv`, `torusRP2OrbitFreeGroupEquiv`,
  `torusRP2SkeletonFundamentalGroupEquivWedge`). Renaming any of these breaks the
  blueprint. Once the leaves land, the subdivision effort becomes redundant.
- G3: the sign `s = ±1` between `circlePositiveFundamentalClass` and
  `apm_t92J05_circlePositiveClass` may need a short lemma. Either sign gives an
  injective `FreeGroup.lift (of i ^ s)`.
- G1/G2: `simp` normalisation of `Surfaces.edgePoint` against `edgePointCircle`
  (`(i : ℕ)` casts, `/ P.edgeCount`). t97J04 handled this with
  `Subtype.ext` + `simp [..., X_homeomorph_aux_edgeCount]`. Here the edge count is
  symbolic, so `simp` may need `Nat.cast` lemmas only.

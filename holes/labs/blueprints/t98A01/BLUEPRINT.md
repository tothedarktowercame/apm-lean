# Blueprint for t98A01 (claude-14, 2026-10-17)

The previous blueprint (2026-10-16, 12 leaves) and its `RevisedMain.lean`
proposal are in `old-2026-10-16/`. That proposal is now the registered
`Main.lean`.

## Verdict

The statement is unchanged. `Blueprint.lean` copies the registered
`Main.lean` block byte for byte. The statement is true.

- (a) `(x, y) ↦ (5x, y)` is a regular 5-sheeted cover of the torus. Among
  closed orientable surfaces only the torus covers itself 5 times.
- (b) T, P and K are the torus, the projective plane and the Klein bottle.
  K#T#T#P#K#T has 2 + 2·3 + 1 + 2 = 11 crosscaps, so χ = 2 − 11 = −9.

## Route

**(a) Example.** The covering is the product of the `AddCircle` 5-fold cover
with the identity. The fibres are cosets of the 5-torsion, whose card is
banked. The deck maps are translations (proved, `t98A01_torusFive_deck`).

**(a) Only the torus.** This is the π₁/b₁ route of the old blueprint, kept
unchanged and proved (`t98A01_orientable_cover_genus`). It uses
`SurfaceGroupBetti` (Schreier bounds on b₁) and the covering index. Its one
former leaf `t98A01_orientable_data_card` is now proved from the banked
`orientableOrbitEquiv`. The remaining leaf is that `Surface true 0` (the disk)
is simply connected.

**(b) Words: proved, except the two bridges.**

- T₁ = `polygonNF_handleWord 1`, and P = `polygonNF_crosscapWord 1` (by `decide`).
- K₁ takes two banked `cutAndPaste` steps to `a a b⁻¹ b⁻¹`, then the
  crosscap bridge for g = 2.
- The sum word takes 16 banked `cutAndPaste` steps, written out between
  explicit words with `decide` side conditions:
  - K₁ and K₂ take 2 steps each.
  - Each handle after a crosscap pair takes 4 steps (T₁ after (bK₁)⁻¹, T₂
    after aT₁, T₃ after (bK₂)⁻¹).

  The result is `polygonNF_crosscapWord 11 t98A01CrosscapLetters`, and then the
  crosscap bridge gives `Surface false 11`.
- This replaces the old generic `kleinBlock` and `handleAbsorb` leaves. The
  same moves are applied concretely, so no generic list lemmas are needed.

**(b) χ.** Integral homology of any one-vertex pairing space is banked
(`PolygonSurfaceHomology.polygonQuotient_homology`: H₀ ≅ ℤ, H₁ ≅ coker,
H₂ ≅ ker, H_{≥3} = 0). The route has four parts:

- Three universal-coefficient leaves pass to ℚ by extension of scalars.
- One leaf gives the integral ranks for the standard data: 2g and 1 when
  orientable, g − 1 and 0 when not.
- The rest is proved: trace of the identity = rank, χ from ranks, homeomorphism
  invariance, and χ(Surface o g) = `eulerCharacteristic o g`.
- The sum surface gets χ = −9 along the normal-form homeomorphism.

## Leaves (8)

| leaf | content | est. lines | banked lemmas used | shared? |
|---|---|---|---|---|
| `t98A01_torusFive_isNfoldCover` | `(5x, y)` is a covering; every fibre has 5 points | 40–100 | `ProductEvenlyCoveredTrivialization.isCoveringMap_productMap`, `AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero`, `UnitAddCircleFiveTorsionCardinality.fiveKernel_natCard` | no |
| `t98A01_surfaceTrueZero_pi1_subsingleton` | `Surface true 0` is the disk, so π₁ is trivial | 40–100 | `polygonNF_homeomorph_of_fibres` (proved helper) | no |
| `polygonNF_crosscap_eqvGen_iff` | `WordRel` of `c₀c₀⋯c_{g−1}c_{g−1}` (distinct labels) and `SurfaceRel false g` generate the same equivalence relation | 80–160 | template `PolygonMoves.crosscapTwo_bridge_aux_eqv` | **shared** (t94J09) |
| `polygonNF_handle_eqvGen_iff` | the same for `a₀b₀a₀⁻¹b₀⁻¹⋯` and `SurfaceRel true g` | 100–200 | same template | family (later t94J04, t00A02) |
| `ratUC_chainIso` | UC (i): `F(C(X;ℤ)) ≅ C(X;ℚ)` for `F = extendScalars ℤ → ℚ` | 100–220 | Mathlib `map_alternatingFaceMapComplex`, `PreservesCoproduct.iso` | library (any rational-χ consumer) |
| `ratUC_homologyIso` | UC (ii): `F` commutes with homology of any ℤ-chain complex (ℚ is flat) | 60–150 | Mathlib `Functor.preservesHomology_of_map_exact`, `ShortComplex.mapHomologyIso` | library |
| `ratUC_finrank` | UC (iii): `ℚ ⊗ M` is finite dimensional of dimension `finrank ℤ M` for finitely generated `M` | 60–150 | Mathlib base change and PID structure theorem | library |
| `polygonNF_standard_boundary_ranks` | the standard data's cokernel is finite of rank 2g (orientable) or g − 1, and the kernel has rank 1 or 0 | 80–200 | `orientableOrbitEquiv`, `nonorientableOrbitEquiv`, `SurfaceGroupBetti.standard_nonorientable_data(_aux_degree)` | family |

Layer-2 declarations (they depend on leaves) are all proved:

- `ratUC_rationalHomology_finrank` (uses UC i–iii).
- `polygonNF_hasEulerCharacteristic_pairingSpace` and
  `polygonNF_hasEulerCharacteristic_surface` (use the ranks leaf and UC).
- `polygonNF_crosscapBridge`, `polygonNF_handleBridge` (use the bridge leaves).
- `t98A01_orientable_cover_genus` (uses the disk leaf).
- `t98A01_sum_normalForm`, `t98A01_klein_bridge`, `t98A01_torus_bridge`,
  `t98A01_projective_bridge`, `t98A01_sum_hasEulerCharacteristic`, and
  `apm_t98a01`.

All leaves are layer 1: no leaf depends on another leaf. Seats can work on all
eight in parallel.

Other banked declarations used (all checked with `#print axioms`: only
`propext`, `Classical.choice`, `Quot.sound`): `PolygonMoves.cutAndPaste`,
`PolygonMoves.homeomorph_trans`,
`PolygonSurfaceHomology.polygonQuotient_homology`,
`PolygonSurfacePiOne.standardPairingData_space_homeomorph`,
`PolygonSurfacePiOne.orientableOrbitEquiv`, `polygon_presentation`,
`SurfaceGroupBetti.b1_finiteIndex_bounds` (and the other b₁ lemmas of part
(a)), `coveringFiberCard_eq_index`.

### Compared with the old blueprint (12 leaves → 8)

- Now proved (6): `t98A01_orientable_data_card`, `t98A01_kleinBlock`,
  `t98A01_handleAbsorb` and `t98A01_sum_normalForm` (as concrete banked move
  chains), `t98A01_hasEulerCharacteristic_crosscap` (now
  `polygonNF_hasEulerCharacteristic_surface`, both orientations), and
  `t98A01_hasEulerCharacteristic_of_homeomorph`.
- Generalized (3):
  - `t98A01_torus_bridge` → `polygonNF_handle_eqvGen_iff` (all g).
  - `t98A01_crosscap_bridge` → `polygonNF_crosscap_eqvGen_iff` (all g, no `0 < g`).
  - `t98A01_crosscap_homology_ranks` → `polygonNF_standard_boundary_ranks`
    (both orientations).
- Split (1): `t98A01_rationalHomology_finrank` (est. 400–900) → three UC
  leaves. Their assembly is proved.
- Kept (2): `t98A01_torusFive_isNfoldCover` (smaller now: the 5-torsion card
  is banked) and `t98A01_surfaceTrueZero_pi1_subsingleton`.

## Shared polygon normal-form leaves

The section `Shared polygon normal-form material (polygonNF_*)` is byte-identical
in this file and in `t94J09/Blueprint.lean` (checked by script).

| declaration | kind | consumers |
|---|---|---|
| `polygonNF_homeomorph_of_fibres`, `polygonNF_quotient_homeomorph` | proved helpers | t98A01, t94J09; any disk-quotient bridge |
| `polygonNF_cutStep`, `polygonNF_uncutStep`, `polygonNF_cancelStep` | proved helpers (banked moves between explicit words) | t98A01, t94J09 |
| `polygonNF_crosscapWord`, `polygonNF_crosscapBridge` | definition, proved from the leaf | t98A01, t94J09 |
| `polygonNF_crosscap_eqvGen_iff` | **leaf** | t98A01 (g = 1, 2, 11), t94J09 (g = 6) |

The family declarations below are in this file only, because t94J09 does not
need them:

| declaration | kind | consumers |
|---|---|---|
| `polygonNF_handleWord`, `polygonNF_handle_eqvGen_iff`, `polygonNF_handleBridge` | definition, **leaf**, proved | t98A01 (g = 1); t94J04 (`Surface true 2`), t00A02 (`Surface true 5`) |
| `polygonNF_standard_boundary_ranks` | **leaf** | t98A01; any χ of a standard surface |
| `polygonNF_trace_induced_id`, `polygonNF_hasEulerCharacteristic_of_finrank`, `polygonNF_hasEulerCharacteristic_of_homeomorph`, `polygonNF_hasEulerCharacteristic_pairingSpace`, `polygonNF_hasEulerCharacteristic_surface` | proved | t98A01; t94J04 and t00A02 if their covering arguments use rational χ |
| `ratUC_*` | three leaves plus a proved assembly | any rational-χ consumer (t99J05, t91J05, t96A01, …) |

For t94J04 and t00A02 the missing piece is an orientable normal form for the
words of their covering surfaces. That needs a cut along an untwisted pair,
which no banked move provides (see Risks).

## Truth checks

- **Fibres.** The fibre over (x, y) is {a | 5a = x} × {y}. That is a coset of
  the 5-torsion {j/5}, so it has 5 points. The covering is a product of
  coverings.
- **Disk.** `SurfaceRel true 0` requires j < 0, so it is empty. The quotient
  is the disk, which is contractible.
- **Crosscap leaf.** Distinct positions with the same label are exactly
  2j, 2j+1. They have equal signs, so the gluing is t ↦ t, as in
  `SurfaceRel false g`. In the case g = 0 both relations are empty.
- **Handle leaf.** Distinct positions with the same label are exactly
  {4j, 4j+2} and {4j+1, 4j+3}. They have opposite signs, so the gluing is
  t ↦ 1 − t, as in `SurfaceRel true g`. In the case g = 0 both relations are
  empty. The g = 1 instance with T₁'s labels discharges the injectivity
  hypothesis by `decide`.
- **Ranks leaf.** `handleSign` is false, false, true, true, and `handlePair`
  is (0 2)(1 3). Each orientable orbit has one +1 and one −1, so the degree
  is 0. The kernel is all of ℤ (rank 1) and the cokernel is ℤ^{2g}. In the
  nonorientable case every sign is false, so the degree is −2 on each of the
  g orbits. Then the kernel is 0 and the cokernel has rank g − 1. Both need
  g > 0, which is a hypothesis. Then χ = 1 − 2g + 1 or 1 − (g − 1).
- **UC leaves.** These are standard facts: chains of free modules, flatness
  of ℚ over ℤ, and torsion vanishing under ℚ ⊗. In the case M = 0 both sides
  are 0. `ratUC_homologyIso` is stated for every ℤ-chain complex, which is
  true because ℚ is flat.
- **Normal form.** The 16-step result is the old blueprint's hand-checked
  `t98A01CrosscapLetters`. Lean now checks every step.

## Checks

- `flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=16G nice lake env lean holes/labs/blueprints/t98A01/Blueprint.lean`:
  0 errors. `declaration uses sorry` appears exactly 8 times, on the 8 leaves.
  `#print axioms` shows that every `t98A01_move*`, `t98A01Klein_move*`,
  `t98A01_orientable_data_card` and the χ invariance lemmas are sorry-free.
- The statement block (82 lines) and the theorem signature (13 lines) are
  identical to `problems/t98A01/lean/Main.lean` (script diff).
- `decide` over the 22-letter words is fast. The whole file elaborates in
  about 5 s, including the 16 steps.

## Risks

- `ratUC_chainIso` is the largest leaf. `ModuleCat.extendScalars` has no
  `Functor.Additive` instance in this Mathlib (instance search fails), but
  `PreservesZeroMorphisms` is found, which is all that `mapHomologicalComplex`
  needs. If the seat needs additivity, it follows from the adjunction.
- `ratUC_homologyIso` needs exactness of extension of scalars along ℤ → ℚ.
  If no flatness-to-`PreservesHomology` bridge exists, the seat proves
  preservation of kernels directly (localization is exact,
  `IsLocalizedModule`).
- In both bridge leaves, `WordRel` uses `edgePoint w.length`. The word length
  is `2g` or `4g` only propositionally.
- I checked the coefficient library (`Coefficient*.lean`) as an alternative.
  `CoefficientH0.SingularHomology R` is Mathlib's
  `singularHomologyFunctor (ModuleCat R)`, the same object as
  `RationalLefschetz.Homology` when R = ℚ. But no module relates ℤ and ℚ
  coefficients (no `extendScalars`, tensor or flatness comparison).
  `PolygonSurfaceHomology` is ℤ-specific (`IntegralSingularHomologyComparison`,
  circle Hurewicz), and redoing it over ℚ is not seat-sized. The
  covering-transfer pattern of `RP3RationalHomology.lean` would need the
  rational homology of the orientable double cover Σ_{g−1}, plus a −1 deck
  action on H₂. That costs more than the three UC leaves.

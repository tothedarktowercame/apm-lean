# Blueprint for t95J03 (claude-14, revision 2026-10-16)

The 2026-10-13 blueprint (three LIBRARY lemmas on an Euler-characteristic route,
plus the statement repair) is archived in `old-2026-10-13/`. The repaired
statement was graded faithful and admitted on 10-13. It is unchanged:
`apm_t95j03` and its definitions are byte-identical to `Main.lean`.

## Verdict

The statement is true. For k > 1:

- S_k = {T, K} if k is even, and {K} if k is odd.
- K is in S_k: use any k-fold cover of K on both sides.
- T is in S_k exactly when k is even:
  - k even: m copies of the torus, k = 2m, cover T (each copy 2-fold) and cover
    K (each copy by the orientation double cover).
  - k odd: every component of a common cover is a finite cover of T, so its π₁
    is abelian. The same component's π₁ is then an abelian finite-index
    subgroup of π₁(K), which has even index. Summing over components, k is even.
- No other surface is in S_k (route below).

Disconnected covers are allowed by the statement and are handled
component-by-component.

## Route: π₁ and b₁ (no Euler characteristic)

`b₁(G) = dim_ℚ Hom(G, ℚ)`, with the t91A02 machinery banked as
`ConstructionTargets/SurfaceGroupBetti.lean`.

Fix the common total space E. It carries p : E → F and q' = q ∘ φ : E → K, both
k-sheeted. For a point e of E, write d_p(e) and d_q(e) for the number of sheets
of its path component.

1. **C1.** π₁(E, e) is a subgroup of π₁(F) of index d_p(e), and of π₁(K) of
   index d_q(e).
2. **Against K** (π₁ ≅ F₂/⟪r⟫, r rationally nonzero): 1 ≤ b₁(π₁(E,e)) ≤ d_q(e).
3. **Against F with n generators:** (n−2)·d_p(e) + 1 ≤ b₁.
   - n ≥ 3 (orientable genus ≥ 2, or nonorientable genus ≥ 3) gives
     d_p < d_q on every component. C3 sums over components:
     k = Σ d_p < Σ d_q = k, a contradiction.
   - RP² (n = 1, relator nonzero) gives b₁ ≤ 0, contradicting step 2.
   - For S², π₁ is trivial, so b₁ = 0, also a contradiction.
4. **Torus parity.** π₁(T) is abelian (S3), so every component's π₁ is an
   abelian finite-index subgroup of π₁(K) ≅ ⟨a,b | b⁻¹aba⟩ ≅ ℤ⋊ℤ. Its index is
   even (S4, orientation character), so k is even (C4).

π₁(K) ≅ PresentedKleinGroup at every basepoint is banked from the closed t93J03
as `ConstructionTargets/KleinBottlePiOne.lean`.

The whole case analysis and both directions of the set equality are sorry-free
assemblies (`t95J03_classify`, `t95J03_realize`, `apm_t95j03`).

## Leaves (13)

| leaf | content | est. lines |
|---|---|---|
| C1 `t95J03_componentFiberCard_eq_index` | index = component sheets (no connectedness; copy `coveringFiberEquivCosets`) | 60–120 |
| C2 `t95J03_componentFiberCard_joined` | component sheets constant along paths | 60–120 |
| C3 `t95J03_sheets_lt_absurd` | summation over components | 100–200 |
| C4 `t95J03_even_sheets` | even classes ⇒ even fibre | 50–100 |
| C5 `t95J03_isKSheeted_comp_homeomorph` | precomposition | 20–50 |
| C6 `t95J03_homeomorph_comp_isKSheeted` | postcomposition | 20–50 |
| C7 `t95J03_isKSheeted_prod_fin` | m copies: d·m sheets | 40–90 |
| C8 `t95J03_id_isKSheeted` | identity | 10–30 |
| S1 `t95J03_orientable_data_card` | **proved** (ported from the t98A01 blueprint, 2026-10-17) | — |
| S2 `t95J03_torus_bridge` | **LIBRARY-sized**: `Surface true 1 ≃ₜ (ℝ/ℤ)²` via `klein_cut_chart` | 250–500 |
| S3 `t95J03_torus_pi1_comm` | **layer 2** (uses S2): π₁(T) commutative | 60–200 |
| S4 `t95J03_klein_index_even` | abelian finite-index subgroup of ℤ⋊ℤ has even index | 100–180 |
| S5 `t95J03_torusNsmul_isKSheeted` | (x,y) ↦ (nx, y) is n-sheeted (as t98A01 a1) | 60–150 |
| S6 `t95J03_klein_doubleCover` | T → K double cover via the plane model | 150–350 |

Truth checks done by hand:

- **C3** needs both bases path-connected, since every component must meet both
  fibres. That is a hypothesis.
- **C4** needs a point of Y. That is a hypothesis.
- **C7** holds for m = 0 (empty cover).
- **S4** examples: ⟨a, b²⟩ has index 2, ⟨a³, b²⟩ has index 6. The odd-index
  subgroup ⟨a, b³⟩ ≅ K is nonabelian.
- **S2:** the chart images of glued boundary points differ by the lattice
  vectors (1,1) and (−1,1). For example, the ℓ¹-normalizations of e^{iθ} and
  e^{i(3π/2−θ)} differ by (1,1).

## Checks

- `Blueprint.lean` compiles: 0 errors, and `declaration uses sorry` appears on
  exactly the 13 leaves (S1 proved 2026-10-17).
- The statement block is identical to Main (checked with `diff`).

## Shared with t98A01 (prove once, copy)

S1 = `t98A01_orientable_data_card` (now proved in both). S5 ≈ `t98A01_torusFive_isNfoldCover`: whichever closes first, the other is a `5 → n` edit.

## Risks

- S2 is the largest piece. Split it if a seat comes back partial: descends /
  injective / surjective / `homeoOfEquivCompactToT2`.
- S6 needs the quotient of the torus by a free involution to be a covering, and
  identified with `KleinPlaneQuotient`. Mathlib's
  `isCoveringMap_quotientMk_of_properlyDiscontinuousSMul` covers the first part.

## Bank recheck (2026-10-17, after merging master)

I re-searched the material banked by the topology loops. Already used:
`CoveringMonodromyCosets`, `T99J01ComponentSheetBounds`,
`CoveringPathComponentSurjective`. Considered and rejected:

- C1 via `RestrictPathComponent.IsCoveringMap.restrictPathComponent` plus
  `coveringFiberCard_eq_index`. It needs `LocPathConnectedSpace` on the base,
  which is not banked for `Surface`, so it adds a leaf rather than removing one.
- No banked polygon-torus ≅ `AddCircle²` bridge (S2) or torus → Klein double
  cover (S6). `TorusPiOneWindingCoordinates` works on `AddCircle²` directly and
  can help S3 once S2 exists.

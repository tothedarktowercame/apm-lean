# Blueprint for t98A01 (claude-14, 2026-10-16)

## Statement

The current `Main.lean` is unregistered and was graded **narrower**
(`statement-registry/open-grades-3.md`, `triage-3.md`). Part (a) is sound. Part
(b) is vacuous as topology for three reasons:

- `connectedSum : Bool → ℕ → Bool → ℕ → Bool × ℕ` writes the rule T#P ≅ P#P#P
  (the substance of "identify the canonical form") into a definition.
- The homeomorphism is `Homeomorph.refl` after `decide`.
- χ is the formula `2 - g`.

`RevisedMain.lean` keeps part (a) verbatim and replaces part (b):

- **Connected sum = word concatenation.** A polygon word `w` presents the
  surface `PolygonMoves.PolygonSurface w`: the disk with its boundary arcs paired,
  equal signs glued `t ↔ t` and opposite signs `t ↔ 1 - t`. For disjoint labels,
  the connected sum of the surfaces of `w₁` and `w₂` is the surface of `w₁ ++ w₂`.
  This is the standard model (Massey Ch. 1 §7). It does not presuppose the
  answer: normalizing the 22-letter word to eleven crosscaps is real
  cut-and-paste work.
- **Words.** T = aba⁻¹b⁻¹, P = aa, K = aba⁻¹b, on labels
  `T98A01Summand × Bool`. The statement checks each word against
  `Surface true 1`, `Surface false 1` and `Surface false 2`.
- **Conclusions.** `T98A01SumSurface ≃ₜ Surface false 11` and
  `HasEulerCharacteristic T98A01SumSurface (-9)`, where `HasEulerCharacteristic`
  is the alternating rank sum of rational singular homology with finiteness
  certificates. It was already graded faithful for t99J05.

The arithmetic checks out. Each K contributes two crosscaps, and a handle next to
a crosscap contributes two, so 2 + 2·3 + 1 + 2 = 11 crosscaps and
χ = 2 − 11 = −9. Equivalently χ = 0 + 0 + 0 + 1 + 0 + 0 − 2·5 = −9.

Outside grade: requested from a read-only Claude grader on 2026-10-16. The result
goes in `statement-registry/t98A01-repair-grade.md`. Install and admit only
after a `faithful` grade: commit Main first, then `admit`, then commit
STATEMENTS.json.

## Route

**(a) Example.** `(x, y) ↦ (5x, y)`:

- covering via Mathlib's `AddCircle` quotient covering ×
  `isCoveringMap_productMap`;
- deck maps are translations by 5-torsion (proved here, `t98A01_torusFive_deck`).

**(a) Only the torus.** This uses the t91A02 route (π₁ and b₁; no χ), now banked
as `ConstructionTargets/SurfaceGroupBetti.lean`. Given a 5-sheeted cover
Σ_g → Σ_h with Σ_g ≅ Σ_h:

- π₁Σ_g is an index-5 subgroup of π₁Σ_h ≅ F_{2h}/⟪r⟫.
- Schreier gives 5(2h−1)+1 ≤ b₁+5.
- Σ_g ≅ Σ_h gives b₁ ≤ 2h. So h = 1.
- Then 2g ≤ b₁+1 ≤ 3 gives g = 1.
- The disk case (h = 0 or g = 0) is excluded because π₁ is trivial.
- Regularity is not used.
- The assembly `t98A01_orientable_cover_genus` is sorry-free.

**(b) Moves.** All moves are by `PolygonMoves.cutAndPaste`
(`u x v x t ≅ u x x v⁻¹ t`, which also works right to left). I checked each step
by hand.

- Klein block, `u a b a⁻¹ b t`:
  - → `u a b b a t` (pair b)
  - → `u a a b⁻¹ b⁻¹ t` (pair a)
- Handle after a crosscap, `u x x a b a⁻¹ b⁻¹ t`:
  - → `u x a⁻¹ x b a⁻¹ b⁻¹ t`
  - → `u x a⁻¹ a⁻¹ b⁻¹ x⁻¹ b⁻¹ t`
  - → `u x a⁻¹ a⁻¹ b⁻¹ b⁻¹ x t`
  - → `u x x b b a a t`
- The sum word applies these in order: K₁, T₁ (x = K₁b⁻¹), T₂ (x = T₁a), K₂,
  T₃ (x = K₂b⁻¹). P is already a crosscap.
- Result: `t98A01CrosscapWord 11 t98A01CrosscapLetters`, then a bridge to
  `SurfaceRel false 11`.

**(b) χ.** The polygon homology already gives integral homology:
`PolygonSurfaceHomology.polygonQuotient_homology` (H₀ ≅ ℤ, H₁ ≅ coker,
H₂ ≅ ker, H_{≥3} = 0). New library work passes this to ℚ by universal
coefficients. Ranks 1, g−1, 0 give χ = 2 − g. Transport along the homeomorphism.

## Leaves (12)

| leaf | content | est. lines |
|---|---|---|
| `t98A01_torusFive_isNfoldCover` | covering + fibres of size 5 | 60–150 |
| `t98A01_orientable_data_card` | standard orientable data has 2g orbits (same as t95J03 S1) | 40–100 |
| `t98A01_surfaceTrueZero_pi1_subsingleton` | `Surface true 0` ≅ disk, simply connected | 40–100 |
| `t98A01_torus_bridge` | `[x,y,x⁻¹,y⁻¹]` ≅ `Surface true 1` (as `crosscapTwo_bridge`) | 60–120 |
| `t98A01_crosscap_bridge` | `c₀c₀…c_{g−1}c_{g−1}` ≅ `Surface false g` | 80–160 |
| `t98A01_kleinBlock` | 2 cut-and-paste steps | 80–180 |
| `t98A01_handleAbsorb` | 4 cut-and-paste steps | 120–220 |
| `t98A01_sum_normalForm` | **layer 2** (uses the two above): concrete chain, side conditions by `decide` | 80–200 |
| `t98A01_rationalHomology_finrank` | **LIBRARY**: universal coefficients ℤ → ℚ | 400–900 |
| `t98A01_crosscap_homology_ranks` | ker 0, coker rank g−1 for the crosscap data | 80–200 |
| `t98A01_hasEulerCharacteristic_crosscap` | **layer 2**: χ(N_g) = 2 − g | 80–160 |
| `t98A01_hasEulerCharacteristic_of_homeomorph` | invariance | 60–120 |

Split `t98A01_rationalHomology_finrank` before dispatch into three pieces:

- (i) a natural chain iso `C(X;ℚ) ≅ extendScalars(C(X;ℤ))`. Chains are
  coproducts of the coefficient object (`SSet.singularChainComplexFunctor`), and
  `extendScalars` preserves coproducts and sends ℤ to ℚ;
- (ii) `extendScalars ℤ → ℚ` is exact (flat), so it preserves homology;
- (iii) `finrank_ℚ (ℚ ⊗ M) = finrank_ℤ M` for finite M.

It is reusable beyond this problem: it is the bridge every rational-χ
statement needs (t91J05, t94J04, t96A01, stage 2).

## Checks

- `Blueprint.lean` compiles: 0 errors, and `declaration uses sorry` appears on
  exactly the 12 leaves.
- The statement block is byte-identical to `RevisedMain.lean`, which also
  compiles.
- The sum word has 22 letters and 11 labels, each used exactly twice
  (`IsPolygonWord`). The anchors' side conditions are proved by `decide`.

## Risks

- The universal-coefficients leaf is the one large piece. With Mathlib it may
  need its own small blueprint (three leaves above).
- `sum_normalForm` relies on `decide` over 22-letter lists. If kernel reduction
  is slow, the seat should prove `IsPolygonWord` by `simp` plus a count lemma.

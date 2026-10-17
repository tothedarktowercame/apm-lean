# Blueprint for t94J09 (claude-14, 2026-10-17)

The previous blueprint (2026-10-13, two LIBRARY leaves) is in
`old-2026-10-13/`.

## Verdict

The statement is unchanged. `Blueprint.lean` copies the registered
`Main.lean` block byte for byte. The statement is true.

- The word has 14 letters, 7 labels and 2 vertex classes, so χ = 2 − 7 + 1 = −4.
- The label `a` occurs twice with the same sign, so the surface is nonorientable.
- So it is N₆, with H₀ = ℤ, H₁ = ℤ⁵ × ℤ/2 and H_k = 0 for k ≥ 2.

Lean now checks this: the normal form below is a compiled chain of banked
moves, and the homology is a banked computation.

## Route

1. **Bridge.** The literal quotient `apm_t94J09_PolygonSurface` is the
   `PolygonMoves` surface of the same word. The word is read letter by letter
   (`pos x ↦ (x, true)`, `neg x ↦ (x, false)`). The only content is that the
   seven generators and `PolygonMoves.WordRel` generate the same equivalence
   relation. That is one leaf. The homeomorphism is then the proved shared
   helper `polygonNF_quotient_homeomorph`.
2. **Normal form: proved.** Five banked `cutAndPaste` steps and one banked
   `inversePairCancellation` step. A breadth-first search over the banked moves
   found the chain, and Lean checks it. No rotation is needed.

   | step | move | result |
   |---|---|---|
   | 0 | — | a c d⁻¹ g⁻¹ f e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ f a b |
   | 1 | cut on a | a a f⁻¹ e g d c b⁻¹ e f⁻¹ g d c⁻¹ b |
   | 2 | cut on f⁻¹ | a a f⁻¹ f⁻¹ e⁻¹ b c⁻¹ d⁻¹ g⁻¹ e⁻¹ g d c⁻¹ b |
   | 3 | cut on e⁻¹ | a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g d c b⁻¹ g d c⁻¹ b |
   | 4 | cut on g | a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b c⁻¹ d⁻¹ d c⁻¹ b |
   | 5 | cut on b | a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b b c d⁻¹ d c |
   | 6 | cancel d⁻¹ d | a a f⁻¹ f⁻¹ e⁻¹ e⁻¹ g g b b c c |

   The cancellation merges the two vertex classes and removes the seventh
   label. Each step's side conditions (freshness, `IsPolygonWord`, list
   equalities) are `decide`.
3. **Crosscap bridge.** The final word is `polygonNF_crosscapWord 6` with six
   distinct letters. The shared leaf gives `Surface false 6`.
4. **N₆ target: proved.** `SurfaceRel false 6 = apm_t94J09_N6Rel` holds by
   `Iff.rfl`. The two `edgePoint`s have the same body and `2 * 6 = 12`.
5. **Homology: proved from the bank.**
   `t94J09Closure.n6PolygonHomologyExplicit` gives H₀ ≅ ℤ,
   H₁ ≅ `(Fin 5 → ℤ) × ZMod 2` and H_k = 0 (k ≥ 2) for `n6PairingData`.
   `standardPairingData_space_homeomorph false 6` and the chain above give
   `n6PairingData.Space ≃ₜ apm_t94J09_PolygonSurface`. The functor sends that
   homeomorphism to isomorphisms in every degree.
6. **Assembly: proved.** The five finite certificates are the lemmas already
   proved in `Main.lean`.

## Leaves (2)

| leaf | content | est. lines | banked lemmas used | shared? |
|---|---|---|---|---|
| `t94J09_polygonRel_eqvGen_iff` | the seven literal generators and `WordRel` of the signed word generate the same equivalence relation | 100–200 | template: `t94J09Closure.frozen_boundaryRel_iff_generator` (the same case split) | no |
| `polygonNF_crosscap_eqvGen_iff` | `WordRel` of `c₀c₀⋯c_{g−1}c_{g−1}` (distinct labels) and `SurfaceRel false g` generate the same equivalence relation | 80–160 | template: `PolygonMoves.crosscapTwo_bridge_aux_eqv` (the case g = 2) | **shared** (t98A01) |

Neither leaf depends on another leaf. There is no layer 2.

Proved here and not leaves: `polygonNF_homeomorph_of_fibres`,
`polygonNF_quotient_homeomorph`, the step wrappers `polygonNF_cutStep`,
`polygonNF_uncutStep`, `polygonNF_cancelStep`, the six moves
`t94J09_move1..6`, `t94J09_word_normalForm`, `t94J09_surface_homeomorph_N6`,
`t94J09_normalization`, `t94J09_polygon_homology`, and `apm_t94j09`.

Banked declarations used (all checked with `#print axioms`: only `propext`,
`Classical.choice`, `Quot.sound`): `PolygonMoves.cutAndPaste`,
`PolygonMoves.inversePairCancellation`, `PolygonMoves.homeomorph_trans`,
`PolygonSurfacePiOne.standardPairingData_space_homeomorph`,
`t94J09Closure.n6PairingData`, `t94J09Closure.n6PolygonHomologyExplicit`.

Compared with the old blueprint, both LIBRARY leaves are gone:

- `apm_t94J09_polygon_normalization` (est. 500–1000 lines) is replaced by the
  two leaves above plus six proved banked moves.
- `apm_t94J09_polygon_homology` (est. 800–1800 lines) is now proved from the
  banked N₆ computation.

## Shared polygon normal-form leaves

The section `Shared polygon normal-form material (polygonNF_*)` is byte-identical
in this file and in `t98A01/Blueprint.lean` (checked by script). It holds:

| declaration | kind | consumers |
|---|---|---|
| `polygonNF_homeomorph_of_fibres` | proved helper | t94J09, t98A01 |
| `polygonNF_quotient_homeomorph` | proved helper | t94J09, t98A01; any disk-quotient bridge |
| `polygonNF_cutStep`, `polygonNF_uncutStep`, `polygonNF_cancelStep` | proved helpers (banked moves between explicit words) | t94J09, t98A01 |
| `polygonNF_crosscapWord` | definition | t94J09, t98A01 |
| `polygonNF_crosscap_eqvGen_iff` | **leaf** | t94J09 (g = 6), t98A01 (g = 1, 2, 11) |
| `polygonNF_crosscapBridge` | proved from the leaf | t94J09, t98A01 |

The t98A01 blueprint also holds four `polygonNF_*` family declarations that
t94J09 does not need. They are listed in `t98A01/BLUEPRINT.md`: the handle
bridge and the Euler-characteristic material. Later problems:

- **t94J04, t00A02** (orientable covers of Σ₂, Σ₅). They need the handle bridge
  `polygonNF_handle_eqvGen_iff`, χ of standard surfaces
  (`polygonNF_hasEulerCharacteristic_surface`), and its homeomorphism
  invariance. They also need an orientable normal form, which no banked move
  provides (see Risks).
- Any nonorientable polygon word: the crosscap bridge plus explicit banked
  move chains, as here.

## Truth checks

- **Generators.** Main's seven constructors pair positions (0,12) a, (6,13) b,
  (1,7) c reversed, (2,8) d, (5,10) e, (4,11) f, (3,9) g. The word's signs at
  those positions are equal except for c (+ at 1, − at 7). So `WordRel` uses
  the same parameter except for c, where it uses `reverseParameter`. This
  matches `apm_t94J09_reverse`. No other pair of positions shares a label.
- **Crosscap leaf.** Two distinct positions with the same label are exactly
  2j, 2j+1 (by injectivity). Both have the same sign, so `WordRel` glues
  t ↦ t, which is `SurfaceRel false g`. In the degenerate case g = 0 both
  relations are empty, and the leaf is still true. It has no `0 < g`
  hypothesis.
- **Invariants.** The normal form has 6 crosscaps. χ = 2 − 6 = −4 agrees with
  V − E + F = 2 − 7 + 1. The banked H₁ has rank 5 = 6 − 1 plus one ℤ/2.

## Checks

- `flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=16G nice lake env lean holes/labs/blueprints/t94J09/Blueprint.lean`:
  0 errors. `declaration uses sorry` appears exactly twice, on the two leaves.
  `#print axioms apm_t94j09` gives `[propext, sorryAx, Classical.choice, Quot.sound]`.
  Each `t94J09_move*` is sorry-free.
- The statement block (doc comment through the last lemma before
  `apm_t94j09`, 272 lines) and the theorem signature (14 lines) are identical
  to `problems/t94J09/lean/Main.lean` (script diff).
- `decide` is fast. The whole file elaborates in about 5 s, including the six
  14-letter steps.
- `ConstructionTargets.t94J09Closure` had no olean in this worktree. It was
  built with `lake build ConstructionTargets.t94J09Closure` (100 s).

## Risks

- `t94J09_polygonRel_eqvGen_iff` is a 14 × 14 `fin_cases`. It is mechanical
  but long. If `simp` on `t94J09_signedWord` is slow, unfold `apm_t94J09_word`
  once and use `decide` for the label equalities.
- In the crosscap leaf, `WordRel` uses `edgePoint w.length`. The length of
  `polygonNF_crosscapWord g c` is `2 * g` only propositionally, so the seat
  must rewrite it.
- No banked move handles an untwisted pair (x … x⁻¹) except adjacent
  cancellation and `mergeRepeatedBlock`. This does not affect t94J09. Its
  chain uses only twisted-pair cuts and one adjacent cancellation. It does
  block a general orientable normal form for t94J04 and t00A02, whose words
  have no twisted pairs at all.

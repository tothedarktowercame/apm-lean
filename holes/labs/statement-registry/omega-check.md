# ω (analytic) vs ∞ (smooth) check — 12 registered statements

Date: 2026-09-28. Read-only; nothing built or run.

Basis: pinned Mathlib `Analysis/Calculus/ContDiff/Defs.lean` l.90: `(⊤ : ℕ∞) : WithTop ℕ∞` = `∞`
(C^∞), `⊤ : WithTop ℕ∞` = `ω` (analytic). The order argument of `IsManifold` (IsManifold/Basic.lean:787),
`ContMDiff`/`ContMDiffAt` (ContMDiff/Defs.lean:171,192), `ContDiff` (ContDiff/Defs.lean:1037) and
`IsLocalDiffeomorph(At)` (LocalDiffeomorph.lean:71) all have type `WithTop ℕ∞`. So a bare `⊤` in that slot
is ω; `(⊤ : ℕ∞)` is coerced and is ∞.

"No mathematical loss" below means: the conclusion is purely topological (does not mention the atlas), and
every space covered by the ∞ reading also carries an analytic atlas (Whitney: every smooth manifold,
with or without boundary, has a compatible real-analytic structure), so the ω statement implies the ∞
statement mathematically. It does not follow inside Lean — Whitney's theorem is not in Mathlib — so the fix is
still worth making.

| id | ω used? | where | consequence | fix |
|---|---|---|---|---|
| t00A02 | yes | hypothesis (`IsManifold I2 ⊤ F` on the genus-5 surface) | narrower in Lean; no mathematical loss (conclusion topological) | `⊤` → `∞` (l.204, 220) |
| t00A03 | yes | hypothesis (`IsManifold I2 ⊤ F`) | narrower in Lean; no mathematical loss (conclusion topological) | `⊤` → `∞` (l.217; also bridges l.170, 197, lemma l.79) |
| t01A08 | no — `(⊤ : ℕ∞)` = ∞ | — | unaffected | none |
| t03J06 | no — `(⊤ : ℕ∞)` = ∞ | — | unaffected | none |
| t94J05 | no — `(⊤ : ℕ∞)` = ∞ | — | unaffected | none |
| t95J06 | yes | definition `apm_t95j06_IsCompactOrientableSurface`, used as hypothesis | narrower in Lean; no mathematical loss (intrinsic atlas, homeomorphism conclusion) | `⊤` → `∞` (l.59) |
| t96J06 | yes | definition `apm_t96j06_BoundsThreeManifold`, used under `¬` in the conclusion | weaker claim (only rules out W with an analytic intrinsic atlas); no mathematical loss | `⊤` → `∞` (l.66; bridge l.146) |
| t96J08 | no — `(⊤ : ℕ∞)` = ∞ (in `apm_t96j08_IsExact`) | — | unaffected | none |
| t97J02 | yes | hypothesis (`IsManifold … ⊤ E` on the covering surfaces) | narrower in Lean; no mathematical loss | `⊤` → `∞` (l.160, 168; bridge l.143, 149) |
| t98A02 | yes | hypothesis (`IsManifold I4 ⊤ X₁/X₂`) | narrower in Lean; no extra mathematical loss beyond smoothness (Whitney) | `⊤` → `∞` (l.238, 241) |
| t99J04 | yes | hypotheses (IsManifold, ContMDiff of `f`/`f i`) and conclusion of part (a) (`IsLocalDiffeomorphAt … ⊤`) | genuinely narrower: only analytic functions/maps covered, so the problem's smooth case is not stated; still true (analytic inverse function theorem for (a), compactness argument for (b)) | `⊤` → `∞` everywhere in l.164–183 (and bridges l.125–152) |
| t96J05 | yes | definition `apm_t96j05_IsEmbeddedSmoothSubmanifold` (hypothesis): `IsManifold … ⊤` and `ContMDiff … ⊤` inclusion; conclusion already uses `∞` | genuinely narrower: only submanifolds that are analytic images (the graph of `exp(-1/x²)` is excluded); still true | `⊤` → `∞` (l.40, 41) |

No statement is false because of ω. The only conclusion-side ω (t99J04 part a) is true by the analytic
inverse function theorem, and it sits under an analytic hypothesis.

## Evidence per problem

**t00A02** — `theorem apm_t00a02` l.216, clause 1:
`[ChartedSpace apm_t00A02_E2 F] [IsManifold apm_t00A02_I2 ⊤ F]` (l.220). F universally quantified;
conclusion `Nonempty (E₁ ≃ₜ E₂)` is topological. Any compact genus-5 surface carries an analytic atlas, so
the ω form loses nothing mathematically, but a Lean instance with only a smooth atlas cannot be fed in.

**t00A03** — `theorem apm_t00a03` l.213: `[IsManifold apm_t00a03_I2 ⊤ F]` (l.217). Conclusion is about
curves, homeomorphisms of components to the pants, and `n = 3g-3`: topological. Same assessment as t00A02.

**t01A08** — l.42 `[IsManifold I (⊤ : ℕ∞) X]`, l.44 `ContMDiff I apm_t01a08_I3 (⊤ : ℕ∞) f`. Explicit
ℕ∞ ascription, coerced to ∞. Smooth, as intended.

**t03J06** — l.251 `ContDiff ℝ (⊤ : ℕ∞) omega`, l.256 `ContDiff ℝ (⊤ : ℕ∞) eta` (non-existence of a smooth
primitive). Both ∞. The `⊤` at l.145 is inside a proof (`(2 : ℕ∞) ≤ ⊤`). Unaffected.

**t94J05** — l.119 `ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡 3) (⊤ : ℕ∞) f`. ∞. Unaffected.

**t95J06** — `apm_t95j06_IsCompactOrientableSurface` l.54–63: `∃ charts : ChartedSpace E2 F, …
IsManifold apm_t95j06_I2 ⊤ F ∧ …` (l.59); used as hypothesis of the second clause of `apm_t95j06` (l.138).
The atlas is intrinsic (not tied to S⁵'s smooth structure) and the conclusion is `≃ₜ Circle × Circle`, so
"∃ analytic atlas" and "∃ smooth atlas" pick out the same F (surfaces). Narrower only formally.
(Aside, not an ω issue: because the atlas is intrinsic, the hypothesis is really "F is a topological surface",
not "F is a smooth submanifold of S⁵".)

**t96J06** — `apm_t96j06_BoundsThreeManifold` l.60–68: `IsManifold (𝓡∂ 3) ⊤ W ∧ Subtype.val '' ((𝓡∂ 3).boundary W) = T`
(l.66). Theorem `apm_t96j06 : ¬apm_t96j06_BoundsThreeManifold apm_t96j06_ProductSubspace`. ω sits inside the
negated existential, so the claim only excludes W carrying an analytic intrinsic atlas — weaker than intended.
Every compact smooth 3-manifold with boundary has an analytic structure, so no mathematical loss.

**t96J08** — `apm_t96j08_IsExact` l.49–52: `ContDiff ℝ (⊤ : ℕ∞) (fun q => η q)`. ∞. Statement
`apm_t96j08` (l.359) uses only `IsClosed`, `IsExact`, and an integral. Unaffected.

**t97J02** — `apm_t97j02` l.156: `[IsManifold (modelWithCornersSelf ℝ apm_t97J02_E2) ⊤ E]` in both universal
clauses (l.160, 168). Conclusions are `≃ₜ` to polygon-quotient surfaces. Narrower only formally.

**t98A02** — `apm_t98a02` l.234: `[IsManifold T98A02I4 ⊤ X₁]` (l.238), `[IsManifold T98A02I4 ⊤ X₂]` (l.241).
Conclusion is singular homology of the connected sum. In dimension 4 requiring *any* smooth atlas already
excludes non-smoothable topological 4-manifolds (the problem says "manifolds", so that is a separate
modelling choice). ω excludes nothing further, by Whitney.

**t99J04** — `apm_t99j04` l.162:
part (a) `[IsManifold (𝓘(ℝ, Euclidean n)) ⊤ X]`, `∀ i, ContMDiff … 𝓘(ℝ, ℝ) ⊤ (f i)` →
`IsLocalDiffeomorphAt … ⊤ (apm_t99J04_coordinateMap f) x`;
part (b) `[IsManifold (𝓘(ℝ, E)) ⊤ X]`, `[IsManifold (𝓘(ℝ, E')) ⊤ Y]`, `ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E')) ⊤ f`.
Here the ω is on the *functions*, so it is a real restriction: smooth non-analytic `f` are not covered, and
Whitney does not help (a smooth map need not be analytic in any atlas). (a) as stated also claims an analytic
local diffeomorphism; that is true (analytic inverse function theorem) given analytic inputs. (b) is true
(the compactness/clopen-range argument does not care about ω). So: narrower, true. Fix: every `⊤` → `∞`
in the statement (and the two bridges, which are shaped to feed it; `apm_t99J04_surjective_of_isLocalDiffeomorph`
l.82 also uses `⊤`).

**t96J05** — `apm_t96j05_IsEmbeddedSmoothSubmanifold` l.36–42:
`IsManifold (apm_t96j05_I m) ⊤ X ∧ ContMDiff (apm_t96j05_I m) (apm_t96j05_I n) ⊤ (fun x : X ↦ x.1)` (l.40–41),
used as hypothesis `hX` of `apm_t96j05` (l.190). The conclusion `apm_t96j05_HasSmoothManifoldStructure`
(l.177–181) already uses `∞`, so hypothesis and conclusion use different orders. Requiring the inclusion to be
analytic in some atlas excludes smooth non-analytic submanifolds, so the hypothesis is genuinely narrower; the
theorem remains true (the smooth statement is true via Sard, and this is a special case). Fix: l.40–41 `⊤` → `∞`.
(Aside, not an ω issue: the definition does not require the inclusion to be an immersion or embedding, so it
admits e.g. a cusp curve with parametrising chart; the conclusion is weak enough (some smooth structure on the
level set, any dimension) that this likely does not make it false, but I did not check this.)

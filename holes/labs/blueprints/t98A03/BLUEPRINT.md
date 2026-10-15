# Blueprint for t98A03

## Triage

Verdict: **true and faithful**.  The registered statement is the literal
topological wedge of `Circle × Circle` and real projective two-space, asks for
non-manifoldness, gives the expected free product fundamental group, and asks
for both kinds of connected three-sheeted cover.  This matches every part of
`problem.md`.

I tried the relevant degeneracies.  Neither summand is empty; both chosen
basepoints exist.  At the wedge point, deleting the point from the union of
two sufficiently small disk neighborhoods gives two components, so it cannot
be locally Euclidean in dimension two.  Dimensions zero and one are also
excluded by neighborhoods in either surface summand, and dimensions above two
by local dimension.  The regular action below is genuinely transitive (a
3-cycle); the irregular action is also transitive, but its point stabilizer in
`S₃` is nonnormal.  Thus neither cover assertion is made true by an empty fiber
or disconnected total space.  The already compiled fiber-cardinality lemma
also rules out empty fibers directly.

No solve-loop refutation exists.

## Revision 2026-10-15: library contracts split

The three former LIBRARY lemmas (π₁ and both covers) are now sorry-free
assemblies over 22 seat leaves.  The non-manifold part is fully proved
(`#print axioms apm_t98a03_wedge_not_manifold`: no `sorryAx`); its seven
leaves were proved by seats on 10-13..15 and are kept untouched.

### Reused proved material

* Copied verbatim from the closed `problems/t92J05/lean/Main.lean` (prefix
  `apm_t92J05_` → `apm_t98a03_t92_`): `fundamentalGroup_prod_equiv`, the
  antipodal `ZMod 2` action on `S²`, the homeomorphism
  `S²/± ≃ₜ RP²` (`..._aux_toP/toPQ/toQ`), `projectivePlane_pathConnected`, and
  `bridge_projectivePlane_fundamentalGroup` (π₁(RP², r) ≃* Z/2 at every r).
  Our RP² instance (`coinduced (mk')`) is definitionally t92J05's and
  `ProjectiveSpaceTopology.Space ℝ 2`'s (checked by `rfl`).
* Library: `genericPointWedgeNormalizedFundamentalGroupEquiv`,
  `PointedContraction.prod/homeomorphSymm`, `circleBaseNeighborhood_contraction`,
  `quotientHomeomorphOfRelIff`, `circleFundamentalGroupMulEquivInt`,
  `fundamentalGroupMulEquivOfHomeomorph`.
* Mathlib: `IsCoveringMapOn.of_openPartialHomeomorph` (compact T2 total space,
  T2 base, local homeomorphism ⇒ covering), `IsCoveringMap.eq_of_comp_eq`,
  `Circle.isQuotientCoveringMap_npow`,
  `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`,
  `t2Space_of_properlyDiscontinuousSMul_of_t2Space`.

## Route

**π₁.** `X t₀ r₀ ≃ₜ Wedge t₀ r₀` (relation iff), then point-wedge van Kampen
with explicit contractible neighbourhoods: torus = product of punctured circles
`{z ≠ -c}`; RP² = affine chart `{r | r.rep·r₀.rep ≠ 0}` contracted by the
homogeneous formula `[(1-t)v + t(v·u/u·u)u]` (defined, with all endpoint
identities proved; only continuity is a leaf).  Torus π₁ = Z² via the copied
product equiv; RP² π₁ from t92J05.  Arbitrary basepoints throughout.

**Covers.** Generic glued spaces `Glue σ τ = (A ⊕ B)/(σ j ~ τ j)`, the base
being `Wedge a₀ b₀ = Glue (fun _ : Unit => a₀) (fun _ => b₀)`.  For local
homeomorphisms `p, q` whose basepoint fibres are exactly the glued points,
`glueMap p q` is proved a covering (`apm_t98a03_glueMap_isCoveringMap`) from
openness + local injectivity + Hausdorff + compactness — no evenly-covered
bookkeeping.  Fibre counts and connectivity are generic too.  Then:

* regular: `T² ⊔ (Fin 3 × RP²)`, sheets `(ζᵏ·∛t₀.1, t₀.2) ~ (k, r₀)`, map
  `(z,w) ↦ (z³,w)` ⊔ `snd`; deck `h` = `(z,w) ↦ (ζz,w)` ⊔ `(k,r) ↦ (k+1,r)`;
  regularity = every fibre is `{x, hx, h²x}`.
* irregular: `T² ⊔ (S² ⊔ RP²)`, sheets glued to `r₀`, `s`, `-s`
  (`s` = unit representative); map `z³` ⊔ (antipodal ⊔ id).  Not regular: a
  path `s ⇝ -s` in `S²` and its image loop on the RP² sheet lift the same base
  loop, one closed, one open; `apm_t98a03_no_deck_of_lift_mismatch` (proved)
  forbids a deck map between their starts.
* Both are packaged over `X t₀ r₀` by `apm_t98a03_coverOf` (proved transport
  of covering / fibre-count / regularity along the base homeomorphism).

## Leaves (22) — all independent; dependencies passed as hypotheses

Generic (reusable for any finite point-gluing of covers, e.g. t01A04, t00A02):

| leaf | statement | size |
|---|---|---|
| `glueMk_eq_iff` | classes are glued pairs / singletons (σ, τ injective) | 40–80 |
| `glue_t2Space` | finite gluing of T2 spaces is T2 | 100–180 |
| `glue_connectedSpace` | connected if `A` connected and `B` joined to glued points | 40–80 |
| `glue_homeomorph` | compatible homeos descend | 40–70 |
| `glueMap_isOpenMap` | glued map is open | 70–120 |
| `glueMap_locInj_inl` / `_inr` | local injectivity at unglued points | 50–90 each |
| `glueMap_locInj_glued` | local injectivity at a glued point | 80–140 |
| `glueMap_fiber_inl` / `_inr` / `_base` | fibre cardinalities | 40–80 each |
| `isLocalHomeomorph_sumElim` | `Sum.elim` of local homeos | 30–60 |
| `circleNbhd_contraction` | `{z ≠ -c}` contracts to `c` | 40–80 |
| `rp2Nbhd_isOpen` | affine chart open | 25–50 |
| `rp2Contract_continuous` | the explicit chart contraction is continuous | 80–160 |
| `sphereProj_eq_iff` | `S² → RP²` fibres are `±x` | 30–60 |

Problem-specific:

| leaf | statement | size |
|---|---|---|
| `zeta_pow_injective` | `1, ζ, ζ²` distinct | 25–50 |
| `circle_cube_roots` | `z³ = c³ ↔ z ∈ {c, ζc, ζ²c}` | 50–100 |
| `regular_fiber_orbit` | regular fibres are `h`-orbits | 80–150 |
| `irrQ_eq_iff` | irregular plane-side fibre over `r₀` = glued points | 20–40 |
| `irrQ_fiber_card` | its fibres have 3 points | 30–60 |
| `irregular_paths` | closed vs open lift of one loop | 40–80 |

(All names carry the `apm_t98a03_` prefix.)

## Checks

* Truth, by hand: the gluing classes are exactly pairs because σ, τ are
  injective; `glueMap` is open only because each basepoint fibre is exactly the
  glued set (hypotheses `hpσ`, `hqτ` are included); the chart contraction keeps
  `w·u = v·u ≠ 0`, is degree-1 homogeneous, fixes `r₀`, ends at `r₀`;
  `ζ * ζ² = ζ³ = 1` closes the rotation; regular fibres: over torus points
  `{ζᵏz}`, over plane points `{(k+m, r)}`, over the base the 3 glued classes,
  each one `h`-orbit; irregular: `(123)`-type torus sheets with the RP² loop
  swapping sheets 1,2 and fixing sheet 0, so not normal, matching the S₃
  monodromy of the queue note.
* Compile: 0 errors; `declaration uses sorry` exactly on the 22 leaves;
  `#print axioms` (scratch copy) — `apm_t98a03_wedge_not_manifold`,
  `torus_fundamentalGroup`, `sphereProj_isCoveringMap`, `coverOf_threeFold`,
  `no_deck_of_lift_mismatch` are sorryAx-free; `apm_t98a03` has sorryAx only
  through leaves.  Statement region byte-identical to Main (diff: imports and the
  module docstring only).

## Risks

* `glue_t2Space` and `glueMap_locInj_glued` are the largest; seats should
  extract a shared "open saturated set" helper if it helps.
* `rp2Contract_continuous` needs open-quotient restriction to a saturated open
  set times the interval; `ConstructionTargets.ProjectiveQuotientDescent` has the
  global versions only.
* Leaves state `IsLocalHomeomorph` / `Nat.card` over quotient types defined by
  `def`; seats may need `show`/`change` to unfold `apm_t98a03_Glue`.

# Blueprint for t01J04 (revision 2026-10-17)

The previous revision (2026-10-13) is in `old-2026-10-13/`. It had one leaf for
the whole positive-dimensional case (500 to 1000 lines). That is too large for
one seat. This revision splits that leaf into 11 leaves. Each one fits in a
single session.

## Verdict

The registered statement in `problems/t01J04/lean/Main.lean` is unchanged. The
definitions and the signature of `apm_t01j04` in `Blueprint.lean` are
byte-identical to Main.lean.

The statement is true. The registry grade (repair-grades-2.md) found the right
fix: `[SecondCountableTopology X]` makes Sard available. The conclusion asks for
an embedded manifold with boundary. The atlas must make `Subtype.val` smooth with
injective derivative. The regular sublevel set `{ρ ∘ f ≤ r}` has exactly this
structure.

Smoothness orders: every order is `(⊤ : ℕ∞)`, as in Main. Lean prints it as
`∞`, which is C^∞. One leaf (C2) writes `((⊤ : ℕ∞) : WithTop ℕ∞)`. That is the
same value, because `isManifold_of_contDiffOn` expects that form. No leaf uses
`(⊤ : WithTop ℕ∞)`, which would mean analytic.

## Route

1. Let `φ` be the preferred chart of `Y` at `y`. Set `ρ z = ‖φ z − φ y‖²`.
2. Leaf A1: for small `r > 0`, the chart ball `V = {z ∈ source φ : ρ z < r}` is
   a neighbourhood of `y`. Its closure lies in `U`. Its closure is exactly
   `{z ∈ source φ : ρ z ≤ r}`.
3. Let `W = f⁻¹(source φ)`. This set is open. `h = ρ ∘ f` is smooth on `W`
   (proved here).
4. Leaf A2 (Sard): pick `r` in `(0, a)` that is a regular value of `h` on `W`.
5. Then `S = f⁻¹(cl V) = {x ∈ W : h x ≤ r}`.
6. At each point `x` of `S` we find an ambient chart `ψ` of `X` in the maximal
   atlas, with `x` in its source. On that source, `z ∈ S` holds exactly when
   `0 ≤ ψ z 0`.
   - If `h x < r`, take a chart inside the open set `{h < r}` whose first
     coordinate is positive (leaf B1, then B4).
   - If `h x = r`, the derivative is nonzero. Take a chart whose first
     coordinate is `h x − h` (leaves B5, B2, B3, then B4).
7. Restrict these charts to `S` (leaf C1). They form a half-space atlas. Its
   transition maps are smooth (leaf C2). The inclusion is smooth (leaf C3). The
   inclusion's derivative is injective (leaf C4).
8. The case `n = 0` is proved here. It reuses the old proof: `X` is discrete, so
   every subset is a 0-manifold.

All glue is proved in `Blueprint.lean`: steps 3, 5, 6, the chart bookkeeping,
the charted-space definition, `IsManifold` from C2, the predicate, and the main
theorem.

## Leaves

All leaves are layer 1. No leaf statement mentions another leaf. C3 and C4 take
extra hypotheses (`IsManifold` of the subtype, and the conclusion of C3). The
assembly supplies these. The provers may assume them.

| Leaf | Content | Est. lines | Banked / library lemmas it uses |
|---|---|---|---|
| A1 `apm_t01J04_leaf_chart_ball` | Small chart balls at `y`: they are neighbourhoods, their closures lie in `U`, and each closure is the closed chart ball inside the chart source. | 120–200 | Mathlib only (compact image under `φ.symm`, T2 implies closed, radial approximation) |
| A2 `apm_t01J04_leaf_sard_regular_value` | A function smooth on an open `W` of a second-countable manifold has a regular value in each interval `(0, a)`. | 80–150 | `T93A04ManifoldWork.null_critical` (ConstructionTargets.SardGenuineSmoothManifoldVector), applied on `TopologicalSpace.Opens W` |
| B1 `apm_t01J04_leaf_euclidean_interior` | Near any point of an open `O ⊆ ℝⁿ` there is a smooth local diffeomorphism with first coordinate `> 0`. A translated small ball works. | 40–80 | Mathlib only |
| B2 `apm_t01J04_leaf_linear_first_coordinate` | Given a nonzero functional `ℓ` on `ℝⁿ`, some linear automorphism `D` has `D v 0 = −ℓ v`. | 40–80 | Mathlib only |
| B3 `apm_t01J04_leaf_euclidean_normal_form` | Given such a `D` for `ℓ = dg(p)`, there is a smooth local diffeomorphism `Φ` near `p`, inside `O`, with `Φ v 0 = g p − g v`. | 80–150 | `SardSmoothNeighborhoodImplicitChartProbe.exists_smooth_neighborhood_restriction` (ConstructionTargets.SardSmoothNeighborhoodImplicitChart), plus `HasStrictFDerivAt.toOpenPartialHomeomorph` |
| B4 `apm_t01J04_leaf_trans_mem_maximalAtlas` | A maximal-atlas chart followed by a smooth local diffeomorphism of `ℝⁿ` is again in the maximal atlas. | 40–80 | Mathlib (`mem_maximalAtlas_iff`, groupoid closure under `trans`) |
| B5 `apm_t01J04_leaf_in_chart` | If `h` is smooth on an open `W`, then `h ∘ φₓ.symm` is `ContDiffOn` on `target ∩ φₓ.symm⁻¹ W`. A surjective `mfderiv h x` gives a nonzero `fderiv` at `φₓ x`. | 40–80 | Mathlib only |
| C1 `apm_t01J04_leaf_restrict_chart` | An ambient chart in which `S` is `{v 0 ≥ 0}` restricts to an `OpenPartialHomeomorph S (EuclideanHalfSpace n)`, packaged as `apm_t01J04_bp_HalfSliceChart`. A point `x₀ ∈ S` supplies the junk inverse value. | 80–130 | Mathlib only |
| C2 `apm_t01J04_leaf_overlap` | Transition maps of restricted charts are `ContDiffOn` in the half-space-model sense. On `range I` they equal the ambient transition, which lies in the maximal atlas. | 60–120 | Mathlib (`compatible_of_mem_maximalAtlas`, `range_euclideanHalfSpace`) |
| C3 `apm_t01J04_leaf_smooth_inclusion` | For the restricted atlas, `Subtype.val` is `ContMDiff` into `X`. | 60–120 | Mathlib (`contMDiffOn_iff_of_mem_maximalAtlas` or the chart definition directly) |
| C4 `apm_t01J04_leaf_injective_mfderiv` | For the restricted atlas, `mfderiv val z` is injective at every point, including boundary points. In charts it is `fderivWithin` over the half-space of a transition map with invertible derivative. The half-space has unique derivatives. | 100–200 | Mathlib (`uniqueDiffOn` of a convex set with nonempty interior, `fderivWithin` congruence) |

Total: about 750–1400 lines, spread over 11 independent seats.

Banked declarations already used in sorry-free code here: none. The two imported
modules are there for leaves A2 and B3. Both imported theorems were checked with
`#print axioms`. They depend only on `propext`, `Classical.choice` and
`Quot.sound`. Neither source file contains `sorry`.

The topology-contract worklists have 370 rows that list t01J04 as a consumer or
other-consumer. Almost all of them are the t93A04 Sard campaign. That campaign
ends in `null_critical`, which this blueprint uses. The three rows whose main
consumer is t01J04 are two stopped probes and the open closure program. They
banked nothing specific to t01J04. No banked half-space or regular-domain atlas
exists: no ConstructionTargets file mentions `EuclideanHalfSpace`. The
regular-fiber atlas modules (`ManifoldRegularFiberCharts`, `…GlobalAtlas`) are
the model for Part C, but they are about level sets, not sublevel sets, so they
are not reused directly.

## Truth checks done by hand

- **n = 0.** This case is handled separately and proved. `X` is discrete. Any
  closed neighbourhood `V ⊆ U` works.
- **m = 0.** `ρ ≡ 0`, so `V = source φ = {y}` and `h ≡ 0` on `W`. Every `r > 0`
  is regular, because the level `{h = r}` is empty. Every point of `S = f⁻¹{y}`
  is interior. A1 holds: the closed ball is the whole one-point model.
- **Empty preimage, or y not in the range of f.** Then `S = ∅`. `choose` over an
  empty type is fine, and the atlas is empty. C1 is never called, so its
  hypothesis `x₀ ∈ S` is harmless.
- **Constant f.** `h` is constant on `W`, with value `c`. Sard makes `c` a
  critical value, so `r ≠ c`. Then `S` is empty or all of `W`, and every point
  is interior.
- **f = id on ℝ.** `S = [y − √r, y + √r]` in the chart. At the two endpoints,
  B3 gives first coordinates `r − h` of opposite orientations. C4 at a boundary
  point is an `fderivWithin` on the closed half-space, which is still unique.
- **B3, the first coordinate.** `Φ v = D v + (g p − g v + ℓ v) e₀` gives
  `Φ v 0 = −ℓ v + g p − g v + ℓ v = g p − g v`. Its derivative at `p` is
  `D + (−ℓ + ℓ) e₀ = D`, which is invertible.
- **The slice condition (assembly).** Interior: `source ψ ⊆ W ∩ {h < r} ⊆ S`,
  and `ψ z 0 > 0`. Boundary: `source ψ ⊆ W` and `ψ z 0 = r − h z`, so
  `z ∈ S ⇔ h z ≤ r ⇔ 0 ≤ ψ z 0`. Both are proved in Lean.
- **C1.** The inverse lands in `S` because `ψ (ψ.symm v) 0 = v 0 ≥ 0`. The
  slice condition then applies.
- **A2 needs second countability.** Without it the registry counterexample
  applies (uncountably many sheets of `c + x²`). The leaf assumes
  `[SecondCountableTopology X]`, and so does Main.

## Checks

- Compile command:
  `flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=16G nice lake env lean holes/labs/blueprints/t01J04/Blueprint.lean`.
  Result: 0 errors. There are exactly 11 `declaration uses 'sorry'` warnings, at
  the 11 leaves (lines 70, 109, 124, 135, 148, 164, 179, 297, 308, 349, 367). The
  file has 11 `sorry` tokens, one per leaf. The run takes about 7 s.
- `#print axioms apm_t01j04` gives `[propext, sorryAx, Classical.choice, Quot.sound]`.
  The `sorryAx` comes only from the leaves.
- Diff: Main.lean lines 7–34 (abbreviation and predicate) match Blueprint
  lines 9–36. Main.lean lines 36–61 (the theorem signature up to `:= by`) match
  the corresponding Blueprint lines. Both diffs are empty.

## Risks

- **C4 is the most delicate leaf.** `mfderiv` for a model with corners unfolds
  to `fderivWithin (range I)` of the written-in-charts map. Near a boundary
  point, that map agrees with the ambient transition only on `range I`. The
  prover must use `fderivWithin` congruence on a `nhdsWithin` set, together with
  `UniqueDiffWithinAt` for the half-space. Budget up to 200 lines.
- **A2 crosses from `X` to the open submanifold `W`.** The prover must relate
  `mfderiv` on `Opens W` to `mfderiv` on `X`. If this proves painful, a fallback
  is to apply Sard chart by chart. `null_critical` is stated for a whole
  manifold, so the open-subset route is the intended one.
- **`apm_t01J04_bp_charted` is `@[reducible]`, at the linter's request.** C3 and
  C4 are stated under `letI := apm_t01J04_bp_charted …`. Provers should keep
  that form and not install a different instance.
- **A1 is plain topology, but it is the longest of the Mathlib-only leaves.**
  The closure equality needs the radial approximation `t → 1⁻`. If it gets
  long, split off "the closed chart ball is closed in `Y`" (compact image, T2).

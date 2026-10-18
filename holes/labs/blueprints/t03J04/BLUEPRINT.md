# Blueprint for t03J04 (2026-10-17)

## Statement

`problems/t03J04/lean/Main.lean` is unregistered and has never been graded.
Earlier triage (triage-1, open-grades-2) called it "narrower-acceptable". I
grade it stricter. Each part is true as written, but (a)(i) is vacuous, and
(a)(ii) and (b) are weaker than the problem.

The repairs Main already made are fine and are kept:

- `n ≥ 1`. For n = 0, χ(T⁰) = 1.
- `X` connected. Otherwise extra components make χ(X) arbitrary.
- `T2Space X`. The doubled-point circle is a counterexample without it.
- Orientation dropped. This makes (b) stronger, and it stays true.

Part by part:

- **(a)(i) vacuous.** The conjunct says a function `Torus n → E n` is
  pointwise nonzero. Nothing makes it a vector field: there is no continuity,
  no smoothness, and no link to the charts. Any nonzero constant passes by
  `simp`. Also, the torus charts are free binders, so "smooth" would not even
  refer to the usual torus.
- **(a)(ii) weaker.** χ is defined as `Σ_{k ≤ n} (-1)^k finrank H_k`. But
  `finrank` is 0 on infinite-dimensional spaces, and the sum stops at n. So
  "= 0" does not certify that the homology is finite or vanishes above n. The
  repo's faithful notion, `HasEulerCharacteristic`, carries those
  certificates.
- **(b) weaker.** It has the same junk-value problem. A smaller point: it
  never shows the value 0 is attained.

`RevisedMain.lean` (compiles; its only `sorry` is the main theorem) makes
three changes:

1. **Pin the torus.** Keep the chart binder, and require
   `LieGroup (Model n) ∞ (Fin n → Circle)` for the pointwise group.
   - A topological group has at most one compatible Lie structure: a
     continuous homomorphism between Lie groups is smooth. So this is exactly
     the standard smooth torus.
   - `∞` is `C^∞` (`open scoped ContDiff`), not `ω`.
2. **(a)(i).** The constant field is `mulInvariantVectorField e₁`, the
   left-invariant field of the first coordinate vector. The statement asks
   that it be a `C^∞` section of the tangent bundle, and that its zeros be
   isolated, which is the problem's wording.
3. **(a)(ii) and (b).**
   - Use `HasEulerCharacteristic … 0`.
   - `X` now has the torus's own model. That is the same generality: ℝⁿ
     either way.
   - So `Tⁿ` is itself an admissible `X`. The last conjunct (`id` is a local
     diffeomorphism) records that 0 is attained. Together with (a)(ii), this
     answers "list all possible values" with {0}.
   - `BoundarylessManifold` is dropped, because the model has no boundary.

Outside grade: not yet requested. Install only after a `faithful` grade.

## Verdict

True. The answer to (b) is χ(X) = 0.

- φ is a k-sheeted covering with k ≥ 1.
- χ(Tⁿ) = k·χ(X).
- χ(Tⁿ) = 0, so χ(X) = 0.

## Route

**(a)(i).** Mathlib proves that invariant fields are `C^{minSmoothness 2}`.
The same proof gives `C^∞` for a `C^∞` Lie group (A1). Left translation is a
diffeomorphism, so the field is nowhere zero (A2). So there are no zeros to
isolate.

**(a)(ii).** No Künneth.

- Rational Mayer–Vietoris (`RP3Homology.rationalMayerVietoris`, banked and
  sorry-free) plus a linear-algebra lemma give
  χ(U ∪ V) = χ(U) + χ(V) − χ(U ∩ V), including finiteness of H_*(U ∪ V) (B1).
- Cover S¹ by two arcs. Their overlap is two disjoint arcs. This gives
  χ(S¹ × Y) = χ(Y) + χ(Y) − 2χ(Y) = 0 whenever χ(Y) exists (B6).
- Induct with `T^{m+1} ≃ₜ S¹ × T^m`, starting from χ(point) = 1. This
  assembly is sorry-free.

**(b).**

- φ is a k-sheeted cover with k > 0 (C1). X is compact, as the image of the
  torus.
- Euler multiplicativity for a k-sheeted cover of a base with a finite good
  cover (C2d). The proof is MV induction on the size of the family. Over each
  contractible piece the cover is trivial (C2a), so the preimage of a piece
  has χ = k (C2b).
- X has a finite good cover (C3, the gap).
- Uniqueness of χ (banked `SurfaceGroupBetti.hasEulerCharacteristic_unique`)
  gives k·c = 0, so c = 0. This assembly is sorry-free.

The banked covering transfer (`CoefficientCoveringTransfer`) is **not** used.
`transfer ≫ p_* = k` only makes p_* onto. It does not give χ(E) = kχ(B), as
the codex-13 STOP said. Some finiteness of the base is essential. Example:
S^∞ → RP^∞ is a double cover of spaces with finite rational homology, yet
χ = 1 on both, not 2 = 2·1.

## Leaves (16)

| leaf | content | est. lines | banked lemmas used |
|---|---|---|---|
| A1 `t03J04_mulInvariant_contMDiff` | invariant field is C^∞ on a C^∞ Lie group | 40–80 | Mathlib `contMDiff_mulInvariantVectorField` (copy, order ∞) |
| A2 `t03J04_mulInvariant_ne_zero` | invariant field of v ≠ 0 is nowhere zero | 30–60 | `inverse_mfderiv_mul_left`, `LieGroup.of_le` |
| B1a `t03J04_euler_les` | linear algebra: a bounded long exact sequence; C is finite and bounded; the alternating sum is 0 | 150–250 | `LinearMap.finrank_range_add_finrank_ker` |
| B1b `t03J04_mv_surjective_zero` | `H₀(U) ⊕ H₀(V) → H₀(X)` is onto | 60–150 | `CoefficientH0` generators / point classes |
| B1 `t03J04_hasEuler_mayerVietoris` | **layer 2** (B1a, B1b): χ(U∪V) = χU + χV − χ(U∩V) | 100–200 | `RP3Homology.rationalMayerVietoris`, `mvI`/`mvJ`, `ModuleCat.biprodIsoProd` |
| B2 `t03J04_hasEuler_of_homotopyEquiv` | homotopy invariance of χ | 40–80 | `CoefficientContractiblePair.singularHomologyIsoOfHomotopyEquiv` |
| B3 `t03J04_hasEuler_unit` | χ(point) = 1 | 40–80 | Mathlib `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`, `isZero_…_of_totallyDisconnectedSpace` |
| B4 `t03J04_hasEuler_of_isEmpty` | χ(∅) = 0 | 30–60 | same |
| B5 `t03J04_circle_cover` | S¹∖{1}, S¹∖{−1}, and the open half-circles are contractible; the overlap is their disjoint union | 120–220 | `Circle.exp`, `ContractibleSpace` API |
| B6 `t03J04_hasEuler_circle_prod` | **layer 2** (B1, B2, B4, B5): χ(S¹ × Y) = 0 | 150–250 | `Homeomorph.Set.prod`, `t03J04_hasEuler_prod_contractible` (proved here) |
| C1 `t03J04_localDiffeo_isKSheeted` | φ is a k-sheeted cover, k > 0 | 100–200 | `IsCoveringMapOn.of_openPartialHomeomorph`, `isCoveringMap_iff_isCoveringMapOn_univ`, `t03J04_localDiffeo_surjective` (proved here) |
| C2a `t03J04_trivial_over_contractible` | a cover is trivial over a contractible open set | 120–250 | Mathlib `Topology/Homotopy/Lifting`, `CoveringLiftRestriction.card_lifts` |
| C2b `t03J04_hasEuler_prod_fin` | **layer 2** (B1, B4): χ(U × Fin k) = kχ(U) | 60–120 | — |
| C2c `t03J04_isKSheeted_restrictPreimage` | restriction of a k-sheeted cover | 30–60 | `IsCoveringMap.restrictPreimage` |
| C2d `t03J04_euler_mul_of_goodFamily` | **layer 3** (B1, B2, B4, C2a–c): multiplicativity over a finite good cover | 200–300 | — |
| C3 `t03J04_compact_manifold_goodCover` | a compact smooth manifold has a finite good cover; **split 2026-10-18** into K1–K4, M1–M7a plus this assembly (M7b), see "C3 breakdown" | 180–280 (assembly) | see below |

These are independent and can start now: A1, A2, B1a, B1b, B2, B3, B4, B5,
C1, C2a and C2c. These wait on other leaves: B1 (on B1a, B1b), then B6 and
C2b, then C2d. C3 is independent but not seat-sized.

Sorry-free here:

- `t03J04_hasEuler_of_finrank` (trace of the identity is `finrank`)
- uniqueness of χ
- `t03J04_e1_ne_zero`
- `t03J04_prodContractible`
- `t03J04_torusSucc` (`T^{m+1} ≃ₜ S¹ × T^m`)
- `t03J04_hasEuler_torus_all` (χ(T^m) = [m = 0])
- the model-space `LocPathConnectedSpace` instance
- `t03J04_localDiffeo_surjective` (Main's proof)
- the main assembly


## C3 breakdown (2026-10-18)

C3 was a gap (2000+ lines via geodesic balls). It is now split into 12 seat-sized
leaves that avoid a Riemannian metric. Pinned Mathlib has no metric-existence
theorem, no geodesics and no tubular neighbourhoods, so the geodesic, Whitney-retraction
and transfer routes are rejected. `IsGoodFamily` and C2d are unchanged. Shared
sorry-free definitions in Blueprint.lean: `t03J04_modelEquiv`, `t03J04_coord`,
`t03J04_chartBall`, `t03J04_coordChange`, `t03J04_coordDomain`. Lean leaf names
are `t03J04_C3_*`; C3 itself keeps its statement and is the assembly M7b.

### Route: chart balls below a convexity radius (no Riemannian metric)

Fix a continuous linear equivalence `e : HModel n ≃L[ℝ] F`, where
`F = EuclideanSpace ℝ (Fin n)`. For a chart `φ_β = chartAt _ β` and a point
`z ∈ source φ_β`, define the chart ball

    B β z r := (chartAt _ β).source ∩ (e ∘ chartAt _ β) ⁻¹' Metric.ball (e (chartAt _ β z)) r

The route has three steps.

1. **Analytic core.** Let `g` be C² with invertible derivative at `y₀`. Then
   `y ↦ ‖g y − a‖²` is convex on a ball around `y₀`, for every `a` close to
   `g y₀`. The reason is that along a line, its second derivative is
   `2‖γ'‖² + 2⟪γ − a, γ''⟫`. That is at least `2c²‖w‖² − 2‖γ − a‖·C‖w‖²`,
   which is ≥ 0 once `‖g y − a‖ ≤ c²/C`.

   Apply this to the coordinate change `g = e ∘ φ_β ∘ φ_α.symm ∘ e.symm`. The set
   `e(φ_α(B β z r))` is a sublevel set of that convex function, so it is convex,
   for every `z` near `x` and every small `r`. In other words, a small ball in
   chart β looks convex in chart α.
2. **Compactness.** Take a finite atlas with compact shrinkings `K_β`. Around
   each `x` there is a chart α and a neighbourhood `W_x`, and below some radius
   every β-ball centred in `W_x ∩ K_β` lies in `source α` and is convex there.
   Take a Lebesgue number δ for the finite cover by the `W_x`. Choose `r` so small
   that every chart ball has diameter `< δ/2` (uniform continuity on `K_β`).
3. **The good cover.** The family is the finite set of chart balls `B β z r`,
   with centres `z` taken from a finite subcover of each `K_β`. Suppose some
   members share a point `x`. Then their centres lie within `δ/2` of `x`, so they
   all lie in one `W_{x_j}`. In the chart `α_j`, every member is convex, so the
   intersection is convex (φ is injective on its source). It is nonempty, hence
   contractible, and the chart homeomorphism carries that back to X.

This route needs only first- and second-derivative estimates and point-set
compactness. Mathlib has all of the inputs. It also gives one more fact: every
intersection is contained in a single chart, which C2d does not use.

### Leaves (12)

| leaf | content | est. lines | banked / library lemmas used |
|---|---|---|---|
| K1 `t03J04_C3_convexOn_of_line_deriv2` | `F` is a real normed space, `N` is open and convex, and `f` is `ContDiffOn ℝ 2 f N`. Suppose every `y ∈ N` and `w` give `0 ≤ deriv^[2] (fun t ↦ f (y + t • w)) 0`. Then `ConvexOn ℝ N f`. | 100–180 | `convexOn_of_deriv2_nonneg`, `convexOn_iff_forall_pos` (reduce to lines), `ConvexOn` via `AffineMap.lineMap` |
| K2 `t03J04_C3_line_deriv2_normSq` | `F` is an inner product space and `γ : ℝ → F` has `HasDerivAt γ γ' t` and `HasDerivAt γ' γ'' t` (as functions). Then `t ↦ ‖γ t − a‖²` has second derivative `2‖γ' t‖² + 2⟪γ t − a, γ'' t⟫` at `t`. | 80–150 | `HasDerivAt.norm_sq`, `HasDerivAt.inner`, `real_inner_self_eq_norm_sq` |
| K3 `t03J04_C3_deriv_bounds` | `g : F → F` is `ContDiffOn ℝ 2 g O` with `O` open and `y₀ ∈ O`, and `fderiv ℝ g y₀` is injective. Then `∃ ρ c C > 0` with `ball y₀ ρ ⊆ O`, and for all `y ∈ ball y₀ ρ` and all `w`: `c‖w‖ ≤ ‖fderiv ℝ g y w‖` and `‖fderiv ℝ (fderiv ℝ g) y w w‖ ≤ C‖w‖²`. | 120–200 | `LinearMap.injective_iff_antilipschitz` / `ContinuousLinearMap.exists_antilipschitzWith`-type (finite dim), `ContDiffOn.continuousOn_fderivWithin`, `IsCompact.exists_bound_of_continuousOn` on `closedBall` |
| K4 `t03J04_C3_normSq_convex_near` (layer 2: K1, K2, K3) | Same hypotheses as K3. Then `∃ ε ρ > 0`, `ball y₀ ρ ⊆ O`, such that `∀ a, ‖a − g y₀‖ < ε → ConvexOn ℝ (ball y₀ ρ) (fun y ↦ ‖g y − a‖²)`. | 100–160 | K1–K3; line derivatives of `g` from `fderiv` (chain rule `HasFDerivAt.comp_hasDerivAt`) |
| M1 `t03J04_C3_coordChange` | For `α β : X`, set `g := e ∘ chartAt β ∘ (chartAt α).symm ∘ e.symm`. It is `ContDiffOn ℝ ∞` on the open set `O := e '' ((chartAt α).target ∩ (chartAt α).symm ⁻¹' (chartAt β).source)`, and `fderiv ℝ g y` is injective at each `y ∈ O`. | 120–200 | `contDiffOn_ext_coord_change`; `ModelWithCorners.pi` of `modelWithCornersSelf` acts as the identity (`range = univ`); injectivity from `g' ∘ g = id` on `O` (the chain rule on the inverse change) |
| M2 `t03J04_C3_chartBall_convex_local` (layer 3: K4, M1) | Let `x ∈ (chartAt α).source ∩ (chartAt β).source`. Then `∃ W ∈ 𝓝 x, ∃ r₀ > 0, ∀ z ∈ W, ∀ r ∈ Ioo 0 r₀`: `B β z r ⊆ (chartAt α).source` and `Convex ℝ (e '' (chartAt α '' B β z r))`. | 150–250 | K4 at `y₀ = e (chartAt α x)` applied to `g` of M1; `ConvexOn.convex_lt`; containment `B β z r ⊆ (e ∘ chartAt α)⁻¹' ball y₀ ρ` by continuity of the chart at `x` |
| M3 `t03J04_C3_uniform_at_point` (layer 4: M2) | Let `I : Finset X` and `K : X → Set X`, with `IsClosed (K β)` and `K β ⊆ (chartAt β).source` for `β ∈ I`. Then `∀ x, ∃ W ∈ 𝓝 x, ∃ r₀ > 0, ∀ β ∈ I, ∀ z ∈ W ∩ K β, ∀ r ∈ Ioo 0 r₀`: `B β z r ⊆ (chartAt x).source` and `Convex ℝ (e '' (chartAt x '' B β z r))`. | 80–150 | M2 with `α = x`, for each `β` with `x ∈ K β`; `W` avoids the other `K β` (they are closed); finite `⋂`, `Finset.min'` |
| M4 `t03J04_C3_chartBall_small` | Let `[MetricSpace X]` (compatible), `K` compact with `K ⊆ (chartAt β).source`, and `δ > 0`. Then `∃ r > 0, ∀ z ∈ K, B β z r ⊆ Metric.ball z δ`. | 100–150 | `IsCompact.exists_thickening_subset_open` for `e '' (chartAt β '' K)` inside `e '' target`; `IsCompact.uniformContinuousOn_of_continuous` for `(chartAt β).symm ∘ e.symm` |
| M5 `t03J04_C3_finite_shrunk_atlas` | `X` is compact. Then `∃ I : Finset X, ∃ K : X → Set X`, `(∀ β ∈ I, IsCompact (K β) ∧ K β ⊆ (chartAt β).source)` and `⋃ β ∈ I, interior (K β) = univ`. | 60–100 | `exists_compact_subset` (locally compact, via `ChartedSpace.locallyCompactSpace`), `isCompact_univ.elim_finite_subcover` |
| M6 `t03J04_C3_contractible_of_convex_image` | Let `S ⊆ (chartAt α).source`, `S.Nonempty`, and `Convex ℝ (e '' (chartAt α '' S))`. Then `ContractibleSpace S`. | 60–100 | `OpenPartialHomeomorph.homeomorphOfImageSubsetSource`, `e.toHomeomorph`, `Convex.contractibleSpace`, `Homeomorph.contractibleSpace` |
| M7a `t03J04_C3_good_of_commonChart` (layer 2: M6) | Let `𝒰 : Finset (Set X)` have open members, and suppose every `s ⊆ 𝒰` with a common point `x` has some `α` with all members in `(chartAt α).source` and each `e '' (chartAt α '' U)` convex. Then `t03J04_IsGoodFamily 𝒰`. | 100–160 | `Set.InjOn.image_sInter` / `InjOn.image_biInter_eq` (chart injective on its source), `Convex.sInter`, M6 |
| M7b C3 itself, `t03J04_compact_manifold_goodCover` (layer 5: M3, M4, M5, M7a) | The assembly. Get the metric from `Manifold.metrizableSpace`. Take `I, K` from M5 and `W_x, r₀(x)` from M3. Take a finite subcover `x₁..x_p` of the `W_x`, a Lebesgue number δ, and `r := min(r₀(x_j), r from M4 at δ/2)`. The centres come from finite subcovers of each `K β` by `B β z r`. Check `⋃₀ = univ` and the common-chart hypothesis of M7a. | 180–280 | `lebesgue_number_lemma_of_metric`, `IsCompact.elim_finite_subcover`, `Finset.biUnion`/`Finset.image` bookkeeping |

The total estimate is 1250–2080 lines over 12 leaves. Every leaf is at most 280
lines.

Layers:
- Layer 1, independent, can start now: K1, K2, K3, M1, M4, M5, M6.
- Layer 2: K4 (uses K1, K2, K3) and M7a (uses M6).
- Layer 3: M2 (uses K4, M1).
- Layer 4: M3 (uses M2).
- Layer 5: the C3 assembly M7b (uses M3, M4, M5, M7a).

In Lean, each leaf states its own inputs as hypotheses or calls sorried leaves.
Seats can therefore work on all of them in parallel, as the existing
t03J04 layer-2 leaves already do.

### Cost risks

Every input is in Mathlib. These are the places where the cost might go over
the estimate:

- **Model-space plumbing (M1).** Lean must see `apm_t03J04_Model n`
  (`ModelWithCorners.pi` of selves) as the identity, so that `extChartAt`
  becomes `chartAt`. If `simp` does not see this, add a small M1a
  (`(apm_t03J04_Model n) = id` pointwise, plus `range = univ`, ~40 lines).
- **K1 line reduction.** I did not find a ready-made lemma for "convex on an open
  convex set iff convex on each segment, via the second derivative". If it is
  missing, the reduction is by hand through `AffineMap.lineMap` and
  `ConvexOn.comp_affineMap`. That fits in the estimate, but K1 is the leaf most
  likely to run long. If it does, split it into the line restriction and the
  1-D step.
- **The `B β z r` definition** has to be shared. It should go into Blueprint.lean
  as a sorry-free `def t03J04_chartBall` before any of these leaves is
  dispatched, together with the fixed `e`, e.g.
  `ContinuousLinearEquiv.ofFinrankEq` (finrank of both sides is `n`).
- **Smoothness orders.** The coordinate change is `ContDiffOn ℝ ∞`
  (`(⊤ : ℕ∞)`). K3 and K4 need only order 2; get it with
  `ContDiffOn.of_le (by norm_cast; exact le_top)`. Do not use
  `(⊤ : WithTop ℕ∞)` anywhere (see memory lean-top-is-analytic).

## Truth checks

- **A1, A2.** True for any C^∞ Lie group over ℝ. For n = 0, A2 is vacuous:
  `e₁` does not exist and NeZero excludes the case.
- **B1a.** Finiteness of `C k`:
  - k = 0: `C 0` is the image of `B 0`.
  - k ≥ 1: `C k` is an extension of `range d ⊂ A (k−1)` by `range g ⊂ C k`,
    both finite.
  - Vanishing: for k ≥ N+2, `B k = 0` makes `d (k−1)` injective into
    `A (k−1) = 0`.
  - The sum: it is the alternating sum along
    `0 → C(N+1) → A N → … → C 0 → 0`.
  - Hand-checked at N = 0: `c₁ − a₀ + b₀ − c₀ = 0`.
- **B1b.** True for every X, including empty X: point classes span H₀ and
  each point lies in U or V.
- **B1, B2, B3, B4.** Standard. U ∩ V may be empty.
- **B5.** In ℂ: (S¹∖{1}) ∩ (S¹∖{−1}) = {Im > 0} ⊔ {Im < 0}. Each set is
  `Circle.exp` of an open interval of length at most 2π.
- **B6.** Matches Künneth (χ = 0·χ(Y)). Also true for Y = ∅.
- **Torus induction.** χ(T⁰) = 1; for m ≥ 1, χ(T^m) = 0.
- **C1.**
  - The torus is compact and Hausdorff, and X is Hausdorff. A local homeo
    from a compact space to a Hausdorff one is a covering onto its image,
    and the image is all of X (clopen, X connected).
  - Fibres are finite, and their cardinality is locally constant, hence
    constant. k ≥ 1 by surjectivity.
  - n = 0: X is a point and k = 1.
- **C2a.**
  - k = 0 gives an empty preimage, which is fine.
  - B is locally path-connected, so the open U is too. A contractible U is
    simply connected, so the cover over U is trivial.
- **C2b.** k = 0: the product is empty and χ = 0.
- **C2d.**
  - The empty family gives B = ∅ and E = ∅.
  - Induction step: `{V ∩ U}` is again good, because its intersections are
    intersections of the original family.
  - Singleton step: χ(U) = 1 and χ(p⁻¹U) = k.
- **C3.** True: Bott–Tu Thm 5.1. A compact Hausdorff manifold is paracompact,
  so a Riemannian metric exists, and its geodesically convex balls give the
  cover. Finite intersections of convex sets are convex, hence contractible.
  For n = 0, X is finite and discrete, and the singletons are a good cover.

## Checks

- `RevisedMain.lean`: 0 errors. One `declaration uses sorry`, on `apm_t03j04`.
- `Blueprint.lean`: 0 errors. Exactly 16 `declaration uses sorry` warnings,
  on the 16 leaves at lines 81, 89, 110, 131, 140, 149, 156, 161, 169, 195,
  243, 257, 265, 271, 281 and 292.
- `#print axioms`:
  - `apm_t03j04`: `[propext, sorryAx, Classical.choice, Quot.sound]`.
    `sorryAx` enters only through the leaves.
  - `t03J04_hasEuler_of_finrank`: no `sorryAx`.
- Byte-identical blocks between the two files, checked by script:
  - the definitions, from `open CategoryTheory Filter Topology` to before the
    blueprint section;
  - the statement of `apm_t03j04`, through `:= by`.
- Imported modules are sorry-free: `CP2RationalHomology`,
  `CoefficientContractiblePair`, `CoveringDegree`, `RationalLefschetz`,
  `SurfaceGroupBetti`. The two `sorry` hits in SurfaceGroupBetti are inside
  comments.
- Compile command used: `flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=16G nice lake env lean <file>`.

## Risks

- **C3 is a real gap.** It needs at least:
  - Riemannian metric existence (partition of unity);
  - geodesics / the exponential map;
  - Whitehead convex neighbourhoods;
  - convex ⇒ contractible.

  None of this is in Mathlib. Plan it as its own blueprint, or replace C3 by
  another finite-type input. Options considered and rejected as no cheaper:
  - **Transfer plus traces.** This needs a Lefschetz fixed-point or
    coincidence theorem on the torus, plus `H_*(Tⁿ) = Λ*(ℚⁿ)` naturally.
  - **Bieberbach group theory.** This needs asphericity, Hochschild–Serre,
    and torsion-freeness of π₁(X).
  - **ENR / tubular neighbourhood.**

  One cheaper variant is possible: C2d only needs nonempty intersections to
  be "evenly covered with finite-type homology", not contractible. That does
  not obviously make C3 easier.
- **Lie-group pin.** A grader may object to the `LieGroup` binder. It is
  satisfiable (by the standard product structure) and it is unique. But
  Mathlib has no `IsManifold`/`LieGroup` instance for pi types, so
  non-vacuity is argued, not proved, in Lean. The original Main had the same
  issue with its free `IsManifold` binder.
- **(a)(i) wording.** The field is given explicitly, not existentially. If a
  grader prefers "∃ smooth field with isolated zeros", the leaves still
  apply.
- **B1a and C2d are the largest seats.** If either runs long, split it:
  - B1a into finiteness/vanishing and the alternating sum;
  - C2d into the intersection-family lemma and the MV step.
- **B6 involves subtype-of-subtype work.** The intersection of the two pieces
  is split again inside `↥((U ∩ V) ×ˢ univ)`. State small homeomorphism
  lemmas first.
- **Lost fixture.** codex-13 compiled an `actual_finite_cover` (covering,
  surjective, finite fibres) in `/tmp/T03J04EulerDiagnostic.lean`. That file
  is gone, so C1 must be redone.

## Grade

Outside grade 2026-10-17: **faithful**, no changes required (`statement-registry/t03J04-repair-grade.md`). Installed as Main (c1b3bc0f5) and admitted (13c28cdc6). The statement block of `Blueprint.lean` is now identical to Main.

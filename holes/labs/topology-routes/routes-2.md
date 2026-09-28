# Routes, list 2 (26 problems) — 2026-09-28

Read-only triage. "banked" = ConstructionTargets/ in /home/joe/code/apm-lean. Mathlib paths are
relative to .lake/packages/mathlib/Mathlib.

### t92J08 — ADAPTER — sorries: 3
Needs:
- `apm_t92J08_bridge_1`: compact boundaryless C^∞ manifold, C¹ field ⇒ one ε>0 such that every point has an integral curve on `Ioo (-ε) ε`.
- `apm_t92J08_bridge_2`: no global integral curve of `x²` agrees with `1/(1-t)` on `Iio 1`.
- `apm_t92j08` (main): assembly of conjunct 1 from bridge_1 + globalisation + uniqueness; conjunct 2 is the banked `apm_t92J08_blowupCurve_isMIntegralCurveOn` (already in the file); conjunct 3 = bridge_2.
Reuse: Mathlib `exists_isMIntegralCurve_of_isMIntegralCurveOn` (Geometry/Manifold/IntegralCurve/UniformTime.lean) — takes exactly bridge_1's conclusion; `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` (ExistUnique.lean) for EqOn γ δ on `Ioo a b` (take t₀ = 0); `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` (Analysis/ODE/PicardLindelof.lean) = Euclidean local existence with time uniform over a closed ball of initial points; the proof of `exists_isMIntegralCurveAt_of_contMDiffAt` (ExistUnique.lean:62) is the chart-transport template; `IsMIntegralCurve.continuous`. Nothing relevant in ConstructionTargets/ (rg IsMIntegralCurve: no hits).
Route:
1. `exists_nhds_uniform_isMIntegralCurveOn`: ∀ x₀, ∃ U ∈ 𝓝 x₀, ∃ ε>0, ∀ x ∈ U, ∃ γ, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-ε) ε) — copy of the ExistUnique.lean:62 proof, using the closed-ball Picard–Lindelöf lemma instead of the ₀ version, and shrinking both the ball and ε so the chart curves stay in `interior (extChartAt I x₀).target` (the fiddly part: the continuity-of-f argument must be made uniform in the initial point, e.g. via the Lipschitz/closedBall bound carried by `IsPicardLindelof.of_contDiffAt_one`).
2. bridge_1: finite subcover of the U's (`CompactSpace`, `isCompact_univ.elim_nhds_subcover`), ε := min over the finite set.
3. bridge_2: from `IsMIntegralCurve δ` get `Continuous δ`; `δ t = 1/(1-t)` for t<1 tends to +∞ as t→1⁻ (`tendsto_inv_zero_atTop` composed with `1-t → 0⁺`), contradicting `δ` continuous at 1 (`ContinuousAt.tendsto` + `not_tendsto_atTop_of_tendsto_nhds`).
4. main: conjunct 1: take x := γ 0, `exists_isMIntegralCurve_of_isMIntegralCurveOn` with bridge_1 gives δ, δ 0 = γ 0; `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` with t₀ = 0 gives EqOn (needs δ restricted via `IsMIntegralCurve.isMIntegralCurveOn`). Conjuncts 2,3 by the in-file lemma and bridge_2.
Shared tags: manifold-uniform-local-flow
Doubts: none. Steps 2–4 are DIRECT-sized; step 1 is the only real work (est. 80–150 lines). Model is `EuclideanSpace ℝ (Fin n)`, complete, so `CompleteSpace E` holds.

### t93A06 — FOUNDATION — sorries: 1
Needs (one `sorry`, seven conjuncts):
- a `SmoothAtlas` (ChartedSpace Plane Torus, IsManifold ∞, `projection` a local diffeomorphism) on `Fin 2 → AddCircle 1`;
- fibres of `projection` are integer translates;
- existence + uniqueness of a smooth 2-form `form` on the torus with `pullback projection form = sourceForm`;
- `torusIntegral form = 1/4`; `¬ IsExact form`;
- `IsSmooth primitive`, `exteriorDerivative primitive = sourceForm`, `parallelogramIntegral primitive = 1/4` (on the plane with its self-atlas).
Reuse: `ConstructionTargets.TorusFormTargets` / `ManifoldFormTargets` (vocabulary only; no theorems); Mathlib `AddCircle.openPartialHomeomorphCoe` (Topology/Instances/AddCircle/Defs.lean:391, chart `Ioo a (a+1) ≅ {↑a}ᶜ`), `piChartedSpace` (ChartedSpace.lean:469; `ModelPi (fun _ => ℝ)` is `Fin 2 → ℝ`), `AddCircle.coe_eq_coe_iff_of_mem_Ico`/`QuotientAddGroup.eq` for fibres, `extDeriv`, `integral_cos_sq`/`integral_sin_sq`, `MeasureTheory.integral2_divergence_prod_of_hasFDerivWithinAt_off_countable` (Green on a rectangle). No AddCircle manifold structure in Mathlib or ConstructionTargets (rg: none); t97A05, t97A06, t98J06 import the same TorusFormTargets and will need the same atlas.
Route:
1. `torusAtlas : SmoothAtlas` — charts = inverses of `projection` on open unit boxes (per-coordinate `openPartialHomeomorphCoe`, then `piChartedSpace`); transitions are locally `x ↦ x + k`, k ∈ ℤ² locally constant ⇒ `contDiffOn`; `IsLocalDiffeomorph` because each chart inverse is a restriction of `projection`. Include the lemma `mfderiv projection p = id` (in these charts).
2. fibre lemma: `projection x = projection y ↔ ∃ k, y = x + k` (coordinatewise `AddCircle` coe equality).
3. descent: `form q := sourceForm (any lift)`; well-defined by 1-periodicity of sin²/cos²; smooth in every chart (chart pullback = `sourceForm` translated); uniqueness from surjectivity of `projection` and `mfderiv projection = id`.
4. `torusIntegral form = 1/4`: integrand is sin²(2πx)cos²(2πy)·det I; Fubini on intervals, each factor = 1/2.
5. `¬ IsExact form`: for smooth η on the torus, `pullback projection (exteriorDerivative η) = extDeriv (pullback projection η)` (translation charts), then Green on the unit square with periodic coefficients gives ∫ = 0 ≠ 1/4.
6. primitive: `IsSmooth` on self-atlas (atlas = {refl}); `extDeriv` of `g · dy` evaluated on (e₀,e₁) is ∂ₓg = (1/2 − cos(4πx)/2)cos²(2πy) = sin²(2πx)cos²(2πy).
7. `parallelogramIntegral primitive = 1/4`: horizontal edges contribute 0 (dy = 0); the two slanted edges combine (substitute s = 1−t) to ∫₀¹ ½cos²(2πt) dt = 1/4. I checked this arithmetic by hand; the value 1/4 is right.
Shared tags: torus-quotient-smooth-atlas, periodic-stokes-square
Doubts: none about truth. Step 1 is the bulk and is shared with t97A05/t97A06/t98J06; steps 4, 6, 7 are calculus that could be done in parallel now (they do not need the atlas: 6 and 7 live on the plane).

### t93J01 — DIRECT — sorries: 1
Needs: every continuous f from the product of spheres to ℝ³ misses some sphere of radius r > 0.
Reuse: Mathlib compactness of the product (sphere `CompactSpace` + `Pi.compactSpace`), `isCompact_range`, `Bornology.IsBounded.exists_norm_le`.
Route:
1. Closure probe (COMPILED 2026-09-28, /tmp/route2probe/A.lean, 3.8 s):
   `obtain ⟨C, hC⟩ := (isCompact_range f.continuous).isBounded.exists_norm_le; refine ⟨max C 0 + 1, by positivity, fun x h => ?_⟩; have := hC (f x) ⟨x, rfl⟩; linarith [le_max_left C 0]`
Shared tags: none
Doubts: none.

### t93J03 — HEAVY — sorries: 1
Needs: for every basepoint k of `KleinBottle` (= `Surface false 2`, disk quotient with word aabb), an iso e : π₁(K,k) ≃* ⟨a,b | b⁻¹aba⟩ such that every path-connected, locally path-connected subspace X whose π₁-image lies in e⁻¹⟨a⟩ embeds in ℝ².
Reuse: `ConstructionTargets.TwoOpenFreeProductMapping.groupEquivalence` (van Kampen, but only when U∩V is simply connected — free product, no amalgamation, so it does not give π₁(K) directly); `CircleUniversalCover` (π₁ S¹ ≅ ℤ via lifting); `SimplyConnectedOpenCover`; Mathlib `IsCoveringMap`, path/homotopy lifting (`IsCoveringMap.liftPath`, `IsCoveringMap.exists_lift…`). No π₁ computation for any `Surface` model exists (rg FundamentalGroup ∩ Surface: none).
Route (covering-space route, the lighter of the two):
1. `kleinDeckAction`: the group G = ⟨a,b⟩ acting on ℝ² by a:(x,y)↦(x+1,y)… with b a glide reflection, properly discontinuously and freely; `ℝ² / G ≃ₜ KleinBottle` (explicit homeomorphism from the square fundamental domain to the aabb polygon quotient — sizeable, polygon-word bookkeeping).
2. `fundamentalGroup_quotient_simplyConnected`: π₁(Y/G) ≃* G for a free properly discontinuous action on a simply connected, locally path-connected Y (deck-group theorem; general, reusable).
3. `PresentedKleinGroup ≃* G` (normal form a^m b^n; group-theory, finite).
4. Lifting criterion: for a covering p : Ỹ → K, a path-connected locally path-connected X with π₁-image in p_*π₁(Ỹ) lifts (general, reusable; Mathlib has path lifting but I found no lifting criterion).
5. The cover ℝ²/⟨a⟩ (an open annulus S¹×ℝ) embeds in ℝ²; a lift j̃ with p∘j̃ = inclusion is an embedding because the inclusion is.
Shared tags: deck-group-fundamental-group, covering-lifting-criterion, polygon-quotient-identification
Doubts: statement looks true (⟨a⟩ is the normal fibre subgroup; its cover is an annulus). Size: steps 1, 2, 4 are each substantial (est. 300–800 lines apiece). No lighter route: part (a) forces an honest π₁ computation.

### t93J04 — DIRECT — sorries: 1
Needs: the inclusions S²×{p} and {p}×S² into S²×S² are not homotopic.
Reuse: `ConstructionTargets.SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`, `…singularHomology_map_const_eq_zero`; `ConstructionTargets.CoefficientFirstReflection.topIso ℤ 1 : H₂(euclideanUnitSphere 3; ℤ) ≅ ℤ` (sorry-free chain); Mathlib `ContinuousMap.Homotopic.comp`.
Route (whole proof COMPILED 2026-09-28 as /tmp/route2probe/D.lean, 4 s, imports `ConstructionTargets.CoefficientSphereAntipodal` + `ConstructionTargets.SingularHomologyHomotopy`):
1. `id_ne_zero`: 𝟙 on H₂(S²;ℤ) ≠ 0 (transport `IsZero` along `topIso ℤ 1`).
2. main: compose the homotopy with `fst` (`(Homotopic.refl fst).comp H`, then `simpa`) to get id ≃ const p; apply homotopy invariance and const ⇒ 0 in degree 2; contradiction with step 1.
Shared tags: none
Doubts: none. `apm_t93j04_Sphere` is definitionally `T02A06.euclideanUnitSphere 3`, so no transport was needed.

### t93J06 — DIRECT — sorries: 1
Needs: no nowhere-zero continuous tangent field on S² (n=3 ambient) or S⁴ (n=5 ambient).
Reuse: `ConstructionTargets.CoefficientSphereAntipodal.antipodal_action` (antipodal map acts by (−1)^(n+1) on Hₙ(Sⁿ;R)), `CoefficientFirstReflection.topIso`, `SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`. `apm_t93j06_Sphere n` is definitionally `T02A06.euclideanUnitSphere n`.
Route:
1. `id_not_homotopic_antipodal (m) (hm : Odd m)`: ¬ id ≃ antipodal on `euclideanUnitSphere (m+2)`. COMPILED 2026-09-28 (/tmp/route2probe/C.lean; needs `set_option maxHeartbeats 2000000` — the default times out on unifying `m+1+1` with `m+2`; stating it with `m+2` throughout or a `show` should remove that).
2. `homotopy_of_field`: from v with ⟪v x, x⟫ = 0, v x ≠ 0, the map (t,x) ↦ cos(πt)·x + sin(πt)·‖v x‖⁻¹·v x lands in the unit sphere and is an id ≃ antipodal homotopy (norm² = cos² + sin² by orthogonality; ~40 lines, not yet written).
3. main: apply 1∘2 with m = 1 and m = 3.
Shared tags: none
Doubts: none.

### t94A01 — DIRECT — sorries: 1
Needs: on `∀ _ : ℕ, Icc 0 1`, U is product-open ↔ every point of U has a `rho`-ball inside U.
Reuse: Mathlib `continuous_tsum`, `summable_geometric_of_lt_one`, `Summable.of_norm_bounded`, `Summable.le_tsum`, `nhds_pi`, `Filter.mem_pi`, `Filter.eventually_all_finite`.
Route (whole proof COMPILED 2026-09-28 as /tmp/route2probe/E.lean, 3 s, Mathlib only):
1. `summable_terms`, `single_le` (one weighted coordinate difference ≤ rho).
2. `continuous_rho f` (uniform tsum of continuous terms) ⇒ (←): the rho-ball is a product-open neighbourhood.
3. (→): `nhds_pi` + `Filter.mem_pi` give finitely many coordinate balls; pick ε below every `2^{-(i+1)}·δᵢ` with `eventually_all_finite`; `single_le` finishes.
Shared tags: none
Doubts: none.

### t94A03 — DIRECT — sorries: 1
Needs: ℝ is not a countable union of subsets homeomorphic to `ℕ → Bool`.
Reuse: Mathlib `nonempty_interior_of_iUnion_of_closed` (Baire on ℝ), `Homeomorph.compactSpace`, `Homeomorph.totallyDisconnectedSpace`, `totallyDisconnectedSpace_subtype_iff`, `isPreconnected_Ioo`.
Route (whole proof COMPILED 2026-09-28 as /tmp/route2probe/F.lean, 3 s, Mathlib only):
1. `cantor_isClosed` (compact ⇒ closed).
2. `cantor_interior_empty` (an open interval inside a totally disconnected set would be preconnected with two points).
3. main: Baire.
Shared tags: none
Doubts: none.

### t94A04 — DIRECT — sorries: 1
Needs: U, V open simply connected, U∩V path connected, U∪V = univ ⇒ X simply connected.
Reuse: `ConstructionTargets.SimplyConnectedOpenCover.simplyConnectedSpace_of_union_eq_univ` (banked, sorry-free, Lebesgue-number proof, no van Kampen — matches the problem's restriction). Mathlib `IsSimplyConnected s` is by definition `SimplyConnectedSpace s`.
Route (COMPILED 2026-09-28, /tmp/route2probe/A.lean):
1. add `import ConstructionTargets.SimplyConnectedOpenCover`; proof term
   `simplyConnectedSpace_of_union_eq_univ hU_open hV_open hcover hU_sc hV_sc hinter_pc`.
Shared tags: none
Doubts: none (hU_pc, hV_pc, hinter_nonempty are unused).

### t94A07 — ADAPTER — sorries: 1
Needs (one `sorry`, `hcore`; fixed-set equality and card = 4 are already proved in-file):
- local clauses at each of the four axis points: tangent kernel = span{e₁,e₂}; `fderiv halfTurn p eᵢ = −eᵢ`; det(I − Df) = 4; local index = 1; `IsLefschetzFixedPoint` (no nonzero fixed tangent vector);
- `¬ IsHomotopyToIdentity R r` (no homotopy through the embedded torus from the half-turn to the identity).
Reuse: in-file `apm_t94a07_fixedSet_eq`, `apm_t94a07_fixedPoints_card`; Mathlib `HasFDerivAt.sqrt`, `fderiv` of a continuous linear map (`halfTurn` is linear: `ContinuousLinearMap.fderiv`), `Matrix.det_fin_two`; banked `ConstructionTargets.CoefficientFirstReflection.all_reflections_negative ℤ 1 (i)` (a coordinate reflection acts by −1 on H₁(S¹)), `CoefficientFirstReflection.topIso ℤ 0` (H₁(S¹;ℤ) ≅ ℤ), `SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`, `CoefficientCoordinateReflections.reflectionMap`.
Route:
1. `halfTurn_clm`: `halfTurn` as a `ContinuousLinearMap` (diag(1,−1,−1)); hence `fderiv halfTurn p = halfTurn` and `fderiv … eᵢ = −eᵢ` for i = 1,2; localMatrix = 2·I, det = 4, index = 1.
2. `tangent_eq_span`: at (±(R±r),0,0), `fderiv constraint p = c·proj₀` with c ≠ 0 (sqrt differentiable since p₀² > 0; y,z partials vanish), so ker = {v | v₀ = 0} = span{e₁,e₂}; then IsLefschetzFixedPoint (fixed tangent v has v₁ = −v₁, v₂ = −v₂).
3. `id_not_homotopic_reflection_circle`: ¬ id ≃ reflectionMap 1 on `euclideanUnitSphere 2` (same 10-line argument as the compiled t93J06 probe, degree 1 instead of 2).
4. `halfTurn_not_homotopic`: given H, form G(t,u) = ψ(H t (γ u)) with γ u = ((R+r)u₀,(R+r)u₁,0) (the outer equator, on the torus) and ψ(x,y,z) = (x,y)/‖(x,y)‖ (defined on the torus since √(x²+y²) ≥ R−r > 0). ψ∘γ = id, ψ∘halfTurn∘γ = reflectionMap 1; G restricted to t ∈ [0,1] is a `ContinuousMap.Homotopy`; contradict step 3.
Shared tags: none
Doubts: none. The in-file comment's "H₁ comparison for the embedded torus" is not needed; the projection-to-the-longitude-circle argument avoids torus homology altogether.

### t94A08 — FOUNDATION — sorries: 1
Needs: (conjunct 1 already proved in-file) Σ₁ = {z₀²+z₁²+z₂² = 0} is locally homeomorphic to open subsets of ℝ²; Σ₂ = {z₁²+z₂² = 0} is not, at the node [1:0:0].
Reuse: in-file `apm_t94a08_regularLevelSet_quadratic1`, `apm_t94a08_sigma2_eq_branches`, `apm_t94a08_node_mem_both_branches`; banked `ConstructionTargets.ProjectiveSpaceTopology` (same carrier `Projectivization ℂ (Fin 3 → ℂ)`, topology coinduced from nonzero vectors — only definitions + continuity/surjectivity of the quotient map) and `ComplexProjectiveChartTargets.chartInverse/coordinates` (definitions; `AffineChartConstruction` is an unproved Prop target); Mathlib `isConnected_ball`, `isConnected_compl_singleton_of_one_lt_rank`, `Homeomorph.map_punctured_nhds_eq`. No affine-chart homeomorphism for the coinduced projective topology exists anywhere.
Route:
1. `affineChart_homeomorph`: for i, {p | (rep p) i ≠ 0} is open in the coinduced topology and homeomorphic to ℂ² via z ↦ z/zᵢ (open quotient map from nonzero vectors; independence of the representative). This is the shared foundation.
2. Σ₁ positive: in chart z₀ = 1 the conic is (u+iv)(u−iv) = −1, homeomorphic to ℂ* ⊂ ℂ ≅ ℝ² via a = u+iv; the two points with z₀ = 0 ([0:1:±i]) lie in chart z₁ = 1, same shape. ≈ 2 lemmas once step 1 exists.
3. Σ₂ negative: in chart z₀ = 1, Σ₂ = {w₁ = i w₂} ∪ {w₁ = −i w₂}, two complex lines meeting only at 0; every small neighbourhood of the node minus the node is disconnected (two nonempty relatively open branch pieces), whereas a homeomorphism to an open W ⊆ ℝ² sends a small ball minus its centre (connected, `isConnected_ball` + removing a point in rank 2) to a neighbourhood of the node minus the node that meets both branches. ≈ 2 lemmas.
Shared tags: projective-affine-chart-homeomorph
Doubts: none about truth. The in-file comment says the punctured node neighbourhood has "four local sectors"; that is the real-conic picture. Over ℂ the two branches are real planes and the punctured neighbourhood has two components (annuli). The route above uses only "disconnected", so the proof is unaffected.

### t94A09 — DIRECT — sorries: 1
Needs: only the S² conjunct: no smooth nowhere-zero tangent field on S² (the S³ and torus conjuncts are proved in-file: `apm_t94a09_exists_smoothSphereField_S3`, `apm_t94a09_exists_smoothTorusField_unique_zero`).
Reuse: the same banked chain as t93J06 (`CoefficientSphereAntipodal.antipodal_action`, `CoefficientFirstReflection.topIso`, `SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`); `apm_t94a09_S2` is definitionally `T02A06.euclideanUnitSphere 3`.
Route:
1. From `Vext` ContDiff, V = Vext ∘ val is continuous; feed it to the t93J06 lemmas `homotopy_of_field` + `id_not_homotopic_antipodal 1` (/tmp/route2probe/C.lean).
Shared tags: none (write the hairy-ball lemma once, in ConstructionTargets, and import it from t93J06 and t94A09)
Doubts: none.

### t94A10 — ADAPTER — sorries: 3
Needs:
- `bridge_solidAngle_closed`: ambient extension of ω is differentiable at x ≠ 0 and `extDeriv` vanishes there.
- `bridge_solidAngle_not_exact`: no η on the punctured space with `extDeriv η̃ = ω`.
- main: `⟨closed, not_exact⟩` (trivial once the bridges exist).
Reuse: in-file denominator lemmas; Mathlib `extDeriv_apply`, `extDeriv_pullback` (Analysis/Calculus/DifferentialForm/Basic.lean:260 — the missing "Stokes interface" the in-file comment asks for is not needed), `Filter.EventuallyEq.extDeriv_eq` (ambient extension agrees with a smooth formula near x ≠ 0), `MeasureTheory.integral2_divergence_prod_of_hasFDerivWithinAt_off_countable` (Green on a rectangle), `integral_sin`.
Route:
1. closed: write ω_x(v,w) = f(x)·det(x,v,w) with f = ‖x‖⁻³ on a neighbourhood; `extDeriv_apply` gives 3f·det(u,v,w) + [Df(u)det(x,v,w) − Df(v)det(x,u,w) + Df(w)det(x,u,v)] = 3f·det + Df(x)·det(u,v,w) (3-dim Laplace identity), and Df(x) = −3f (Euler, degree −3). In coordinates: `field_simp; ring` after `HasFDerivAt` for the formula.
2. `pullback_sphere_param`: Φ(s,t) = (sin s cos t, sin s sin t, cos s) maps into the punctured space; (Φ*ω)(s,t)(e₀,e₁) = sin s.
3. not_exact: if dη̃ = ω then Φ*ω = d(Φ*η̃) (`extDeriv_pullback`, needs η̃ differentiable at Φ(s,t), given); Green on [0,π]×[0,2π]: the t-edges cancel by 2π-periodicity, the s-edges vanish because ∂ₜΦ = 0 at s = 0, π. So ∫∫ sin s = 0, but it is 4π.
Shared tags: periodic-stokes-square
Doubts: none. Step 1 is one computation-heavy lemma; step 3's Green application needs care with the countable-exception/integrability side conditions.

### t94J04 — HEAVY — sorries: 2
Needs: (index-1 case is closed in-file) for a compact smooth 2-manifold F with the homology of a closed orientable genus-2 surface, any two subgroups of π₁(F) of the same index k ≥ 2 are isomorphic. `bridge_equal_index_subgroups` states exactly this; the main `sorry` is then one line (`exact apm_t94J04_bridge_equal_index_subgroups hF p k hk2 H K hH hK`).
Reuse: in-file index-1 lemma, coset-count equivalence, Euler-characteristic arithmetic; banked covering-space pieces (`CoveringDegree`, `CoveringLiftRestriction`, `LiteralPullbackCover`) and Mathlib `IsCoveringMap` — none gives the subgroup ↔ cover correspondence or surface classification.
Route:
1. Surface recognition: a closed smooth 2-manifold with H₁ ≅ ℤ⁴, H₂ ≅ ℤ is homeomorphic to Σ₂ (classification of compact surfaces + homology of the standard models). No banked material.
2. Covering correspondence: an index-k subgroup H ≤ π₁(F) gives a connected k-sheeted cover F_H with π₁(F_H) ≅ H (needs existence of covers for subgroups of a locally path-connected, semilocally simply connected space).
3. F_H is a closed orientable surface with χ = kχ(F) = −2k, so F_H ≅ Σ_{k+1} (classification again + multiplicativity of χ under finite covers).
4. π₁ of homeomorphic surfaces are isomorphic ⇒ H ≃* K.
Shared tags: surface-classification, covering-subgroup-correspondence, euler-characteristic-covers
Doubts: the statement is true. A lighter route has not been found: the hypothesis gives F only up to homology, so recognising F (step 1) cannot be skipped. A purely group-theoretic route (Reidemeister–Schreier on the one-relator presentation) still needs π₁(F) ≅ the surface group, which also goes through step 1. Size: classification of surfaces alone is a multi-thousand-line programme.

### t94J09 — HEAVY — sorries: 1
Needs: (combinatorial conjuncts closed in-file) the 14-gon quotient `PolygonSurface` is homeomorphic to the standard 12-gon `N6`, H₀ ≅ ℤ, H₁ ≅ ℤ⁵ × ℤ/2, H_k = 0 for k ≥ 2.
Reuse: in-file `apm_t94J09_homeomorphOfDiskMaps` (reduces a homeomorphism to two disk self-maps respecting the relations; but a cut-and-paste homeomorphism between different polygon words is generally not induced by a single disk map, so this helper is probably not usable as is); banked `ProductionOpenCoverMayerVietoris`, `SingularHomologyConcrete`, sphere/circle homology; nothing computes homology of a polygon quotient.
Route:
1. Homeomorphism: a chain of cut-and-paste moves (the 8 moves in the informal solution, but see Doubts), each an explicit homeomorphism between polygon quotients — tag polygon-cut-and-paste. Alternatively classification + invariants (heavier).
2. Homology: Mayer–Vietoris on (open 2-cell) ∪ (neighbourhood of the 1-skeleton); the 1-skeleton is a graph with 2 vertices and 7 edges ≃ wedge of 6 circles; H₁ = coker(ℤ → ℤ⁶) of the boundary-word abelianisation, H₂ = its kernel (= 0 here), giving ℤ⁵ × ℤ/2 after Smith normal form.
Shared tags: polygon-surface-homology, polygon-cut-and-paste
Doubts: I recomputed the vertex classes of the Lean relation (union-find over the 7 edge pairings): exactly 2 classes, {3,9} and the rest, so χ = 2 − 7 + 1 = −4 and N₆ is right. The informal solution's "connected sum of 3 real projective planes" (from kind.c) is wrong; the frozen statement's N₆, H₁ = ℤ⁵ × ℤ/2 is the correct answer. Do not follow the informal move sequence.

### t94J10 — DIRECT — sorries: 1
Needs: product of regular spaces is regular.
Reuse: Mathlib product instance.
Route: `infer_instance` (COMPILED 2026-09-28, /tmp/route2probe/G.lean).
Shared tags: none
Doubts: none.

### t94J11 — DIRECT — sorries: 1
Needs: for an open equivalence relation, the graph is closed ↔ the quotient is Hausdorff.
Reuse: Mathlib `t2Space_iff_of_isOpenQuotientMap` (Topology/Separation/Hausdorff.lean:170).
Route (COMPILED 2026-09-28, /tmp/route2probe/G.lean):
1. `intro qt hopen; have hq : IsOpenQuotientMap (Quotient.mk' : X → Quotient r) := ⟨Quotient.mk'_surjective, continuous_quot_mk, hopen⟩; rw [t2Space_iff_of_isOpenQuotientMap hq]; simp only [Quotient.eq']`.
Shared tags: none
Doubts: none.

### t95A04 — FOUNDATION — sorries: 1
Needs: a `SmoothAtlas 2` on `Space ℝ 2` (quotient-compatible: `sphereProjection` a local diffeomorphism), and a map f with f∘proj = Veronese map, f smooth, a topological embedding, and `Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ f`.
Reuse: `ConstructionTargets.RealProjectiveSmoothTarget` (the `SmoothAtlas` structure, `sphereProjection`; no inhabitant), `ProjectiveSpaceTopology` (coinduced topology, `continuous_quotientMap`, `surjective_quotientMap`); Mathlib sphere manifold (`EuclideanSpace.instChartedSpaceSphere`, `range_mfderiv_coe_sphere`), `Continuous.isClosedEmbedding` (compact → Hausdorff), `Geometry/Manifold/Immersion.lean` (definition only: its TODO list says "mfderiv injective ⇒ immersion" is not yet in Mathlib).
Route:
1. `rpSmoothAtlas n : SmoothAtlas n` — charts = sphere charts restricted to open hemispheres, composed with the local inverse of `sphereProjection` (a 2-sheeted local homeomorphism for the coinduced topology); transitions are sphere transitions composed with ±id. Shared with t96A07.
2. descend: f [v] := Q(v)/‖v‖² (degree-0 homogeneous, continuous on nonzero vectors, so continuous on the coinduced quotient); agrees with `T95A04SphereMap` on the sphere.
3. `ContMDiff`: f ∘ proj = sphere map is smooth and proj is a local diffeomorphism.
4. embedding: `Space ℝ 2` compact (image of the sphere), f injective (Q(v) = Q(w) on unit vectors ⇒ w = ±v), so `Continuous.isClosedEmbedding`.
5. immersion: d(sphere map) is injective on T_pS² (Du = 0 with u ⊥ p forces u = 0), then the missing general lemma `isImmersion_of_injective_mfderiv` (finite dimension, via the inverse function theorem `HasStrictFDerivAt.toOpenPartialHomeomorph`).
Shared tags: rp-smooth-atlas, immersion-from-injective-mfderiv
Doubts: none about truth. Step 5's general lemma is a Mathlib-sized contribution (Mathlib lists it as TODO); budget it as its own foundation row.

### t95J02 — ADAPTER — sorries: 3
Needs:
- `bridge_vertical_H1_kernel`: a nonzero γ ∈ H₁(B;ℤ) with i_B*(γ) = 0 in H₁(K).
- `bridge_retraction_injective`: a retraction onto B makes H₁(i_B) injective.
- main, second conjunct: combine the two (the first conjunct, retraction onto A, is proved in-file).
Reuse: in-file quotient-point identities (`t95J02QuotientPoint_glide`, `…_vertical`); banked `CoefficientFirstReflection.topIso ℤ 0` (H₁(S¹;ℤ) ≅ ℤ), `CoefficientFirstReflection.all_reflections_negative ℤ 1 1` (y-reflection acts by −1 on H₁(S¹)), `SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`; Mathlib `Functor.map_comp`.
Route:
1. `circleB_homeo : euclideanUnitSphere 2 ≃ₜ CircleB` — forward u ↦ [(0, arg u/2π)] (via the angle map, well defined by `vertical`); inverse is the restriction of the continuous map K → ℝ², [(x,y)] ↦ (cos 2πy, sin 2πy·cos πx), which respects both generators (checked: glide flips both sin 2πy and cos πx). No Hausdorffness of K needed.
2. `beta_homotopic_beta_conj`: β := i_B ∘ circleB_homeo is homotopic to β ∘ reflectionMap 1 via (t,u) ↦ [(t, y(u))] (at t = 1, [(1,y)] = [(0,−y)] by `glide`).
3. bridge 1: H₁(β) = H₁(β)∘(−1), so H₁(β)(2g) = 0 for the generator g; γ := H₁(homeo)(2g) ≠ 0 since H₁(B) ≅ ℤ.
4. bridge 2: r ≫ … : `i ≫ r = 𝟙` ⇒ H₁(i) ≫ H₁(r) = 𝟙 ⇒ injective (5 lines).
5. main: `intro hret; obtain ⟨γ, hγ, h0⟩ := bridge1; exact hγ (bridge2 hret (h0.trans (map_zero _).symm))`.
Shared tags: none
Doubts: none. γ = 2·[B]; the fibre class has order 2 in H₁(K), so the bridge-1 statement is true.

### t95J03 — HEAVY — sorries: 1
Needs: for k > 1, the set of F (in the enum `orientable g | nonorientable g`, interpreted by the polygon models `Surface o g`) sharing a k-sheeted cover (covering map with every fibre of card k; the covering space need NOT be connected) with the Klein bottle is {torus, Klein} for even k and {Klein} for odd k.
Reuse: `ConstructionTargets.Surfaces` (models + the `eulerCharacteristic` table, a definition, not an invariant); in-file `apm_t95j03_previous_encoding` (the Euler-characteristic bookkeeping, conditional on hypotheses that are exactly the missing topology); banked covering pieces (`CoveringDegree`, `CoefficientCoveringTransfer` — rational transfer chain map, usable for χ(E) = k·χ(B)).
Route:
1. Realisation, Klein ∈ set: `Fin k × K → K` (trivial k-sheeted cover), identity homeomorphism.
2. Realisation, torus ∈ set for even k: an explicit 2-sheeted cover torus → Klein on the polygon models (needs a homeomorphism between the aabb / abab⁻¹… polygon models and ℝ²/lattice quotients), then k/2 disjoint copies over both.
3. Exclusion by Euler characteristic: χ(E) = k·χ(F) (rational transfer + finite homology of polygon surfaces) and χ(E) = k·χ(K) = 0, so χ(F) = 0; requires computing H_*(Surface o g; ℚ) for all g (polygon-surface-homology), and treating g = 0 separately (see Doubts).
4. Exclusion of the torus for odd k: every cover of the torus is a union of tori (orientable), while a k-sheeted cover of K with k odd has a component of odd degree, which is nonorientable — needs an orientability invariant (H₂(·;ℤ) of closed surfaces, or the orientation double cover).
Shared tags: polygon-surface-homology, euler-characteristic-covers, polygon-quotient-identification, orientation-double-cover
Doubts: `Surface o 0` has an empty edge relation, so `orientable 0` and `nonorientable 0` both denote the closed DISK, not S² (and the in-file `euler` table gives them 2 and 2). The claimed answer excludes them, which is still true (a disjoint union of disks has boundary / is contractible per component, a cover of K is not), but step 3 cannot use the table's χ for g = 0; the disk needs its own exclusion. Report to the grader as an encoding quirk, not a falsity.

### t95J06 — HEAVY — sorries: 2
Needs: `bridge_1`: every compact subset F ⊆ S⁵ carrying some (abstract) smooth 2-manifold structure, with H₂ of each component ≅ ℤ, invariant under the Hopf circle action, has every component homeomorphic to S¹×S¹. The main `sorry` is `exact bridge_1 …` (invariance of T is proved in-file).
Reuse: in-file flow lemmas (`…_flow_periodic`, `…_flow_add`, `…_flow_zero`); nothing banked on group actions on surfaces.
Route:
1. Each component C of F is invariant and inherits a free continuous S¹-action (the Hopf action is free on S⁵).
2. Local cross-sections for a free S¹-action on a topological 2-manifold (Gleason slice theorem, or a 2-dimensional ad hoc argument): C → C/S¹ is a principal S¹-bundle over a compact 1-manifold, i.e. over S¹.
3. S¹-bundles over S¹ are the torus or the Klein bottle (monodromy ±1).
4. H₂(C;ℤ) ≅ ℤ excludes the Klein bottle (H₂ = 0), so C ≅ S¹×S¹.
Shared tags: free-circle-action-slice, surface-homology-invariants
Doubts: true as encoded (note the charts on F are arbitrary: F is only a topological surface inside S⁵, so no smooth transversality to the orbits is available; step 2 must be topological). Size: step 2 alone is substantial (est. 500+ lines). A lighter route via Euler characteristic (a free S¹-action forces χ = 0, then classification) is not lighter: it needs classification of surfaces.

### t96A01 — HEAVY — sorries: 1
Needs: S homeomorphic to the genus-4 polygon model `Surface true 4`, H ≤ π₁(S,s) of finite index n ⇒ H ≃* `OrientableSurfaceGroup (3n+1)`.
Reuse: `ConstructionTargets.StatementSurfaceModels` (`OrientableSurfaceGroup`, `surfaceRelator`: definitions only); `TwoOpenFreeProductMapping.groupEquivalence` (van Kampen only for simply connected overlap); banked covering pieces. No π₁ of any polygon surface is banked.
Route:
1. π₁(Surface true g) ≃* OrientableSurfaceGroup g — van Kampen with a non-simply-connected (annulus) overlap: disk ∪ (surface minus a point ≃ wedge of 2g circles), amalgamated over ℤ. Needs the amalgamated van Kampen (the banked version is the free-product case) and π₁(wedge of circles) = free group.
2. Covering correspondence: finite-index H gives a connected n-sheeted cover S_H with π₁ ≅ H.
3. S_H is a closed orientable surface with χ = n·(−6), hence ≅ Surface true (3n+1): needs classification of surfaces (or at least: a closed orientable surface with χ = 2−2g is homeomorphic to the genus-g model).
4. Transport along homeomorphisms and step 1 for g = 3n+1.
Shared tags: van-kampen-amalgamated, surface-classification, covering-subgroup-correspondence, euler-characteristic-covers
Doubts: the statement is true for n ≥ 1 (`FiniteIndex` excludes index 0). Same programme as t94J04; no lighter route (the conclusion is an explicit presentation of an arbitrary finite-index subgroup).

### t96A02 — HEAVY — sorries: 1
Needs: every continuous self-map of RP² ∨ RP² (two aa-polygon quotients glued at centre points) has a fixed point.
Reuse: `ConstructionTargets.StatementSurfaceModels.ProjectivePlaneWedge`, `PointWedgeQuotient`; `ConstructionTargets.RationalLefschetz` (the `HasLefschetzNumber` predicate; no fixed-point theorem); `CoefficientCoveringTransfer` (could give H_*(RP²;ℚ) from S²).
Route:
1. H̃_*(RP²;ℚ) = 0 (transfer from S², antipodal acts by −1 on H₂(S²;ℚ): banked `CoefficientSphereAntipodal.antipodal_action`) — requires identifying the aa-polygon model with S²/±1 (polygon-quotient-identification).
2. Wedge: H̃_*(X;ℚ) = H̃(RP²;ℚ)² = 0 (Mayer–Vietoris on the wedge).
3. Hence the rational Lefschetz number of any f is 1.
4. Lefschetz fixed-point theorem for compact polyhedra (or compact ENRs): L(f) ≠ 0 ⇒ fixed point. Not in Mathlib, not banked.
Shared tags: lefschetz-fixed-point-theorem, polygon-quotient-identification, rp-rational-homology
Doubts: statement true. Size: step 4 is a large programme (simplicial approximation + chain-level trace, est. thousands of lines). I did not find a lighter route; an elementary retraction argument does not obviously work because f may swap the two planes.

### t96A04 — DIRECT — sorries: 1
Needs: `C(Icc 0 1, Icc 0 1)` with its (sup-metric) topology is not compact.
Reuse: Mathlib `IsCompact.tendsto_subseq`, `continuous_eval_const`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Set.projIcc`.
Route (whole proof COMPILED 2026-09-28 as /tmp/route2probe/G.lean, Mathlib only):
1. f n x = xⁿ; a convergent subsequence has a limit g with g x = 0 for x < 1 and g 1 = 1 (pointwise limits via evaluation).
2. g ∘ projIcc is continuous at 1 but tends to 0 along (0,1) — contradiction.
Shared tags: none
Doubts: none (Mathlib's topology on `C(I, I)` is compact-open, which equals the sup-metric topology on a compact domain, so the frozen statement means the printed question).

### t96A06 — HEAVY — sorries: 1
Needs: a continuous f̄ : RP³ → RP³ descending the quadratic map; `HasLefschetzNumber f̄ (−3)` (rational homology is finite-dimensional, vanishes above a bound, alternating trace = −3); f̄ not homotopic to id.
Reuse: `ConstructionTargets.ProjectiveSpaceTopology` (coinduced topology), `RationalLefschetz` (predicate), `CoefficientCoveringTransfer.transfer` (rational transfer for a k-sheeted cover), `CoefficientSphereAntipodal.antipodal_action` (antipodal acts by (−1)^(n+1) on Hₙ(Sⁿ)), `CoefficientFirstReflection.topIso`, `SingularHomologyHomotopy.singularHomology_map_eq_of_homotopic`.
Route:
1. descent + continuity: polynomialMap(λv) = λ²·polynomialMap(v) and polynomialMap v = 0 ⇒ v = 0 (DIRECT-sized).
2. H_*(RP³;ℚ): ℚ in degrees 0 and 3, zero otherwise — S³ → RP³ is 2-sheeted (needs this covering statement for the coinduced topology), transfer + antipodal acting by +1 on H₃(S³).
3. deg f̄ = 4 on H₃: f̄ lifts to F(z,w) = (z²,w²)/‖·‖ on S³ ⊂ ℂ², p∘F = f̄∘p, so deg f̄ = deg F; deg F = 4 via join/suspension naturality of the banked sphere shift (F is the join of two degree-2 circle maps) — the hard step.
4. L(f̄) = 1 − 4 = −3; L(id) = 1 − 1 = 0 ≠ −3 plus homotopy invariance of `induced` ⇒ not homotopic.
Shared tags: rp-rational-homology, sphere-map-degree, projective-covering-sphere
Doubts: arithmetic checked (trace on H₃ enters with sign (−1)³). Steps 1, 4 are small; 2 reuses banked transfer; 3 has no banked support.

### t96A07 — FOUNDATION — sorries: 1
Needs: a `SmoothAtlas 2` on RP², the descended map f (f∘proj = (yz,xz,xy)), `ContMDiff` f, ¬(f ⋔ z-axis), and infinitely many z with (sphere map ⋔ horizontal plane z) and z in the image.
Reuse: as t95A04 (`RealProjectiveSmoothTarget`, `ProjectiveSpaceTopology`); Mathlib `range_mfderiv_coe_sphere` (tangent space of the sphere as (ℝ∙p)ᗮ), `mfderiv_comp`, `Set.Ioo_infinite`.
Route:
1. `rpSmoothAtlas 2` (shared with t95A04).
2. descend + smooth, as t95A04 steps 2–3 (f is even: f(−p) = f(p)).
3. ¬ transverse to the axis at [e₀]: f[e₀] = 0 = axis 0; on T_{e₀}S² = {(0,b,c)} the derivative is (0,c,b), range = span{e₁,e₂}; axis adds span{e₂}; sum ≠ ⊤. Needs `range (mfderiv f [p]) = range (d sphereMap on T_pS²)` via the local diffeomorphism (chain rule, mfderiv of proj is an iso).
4. part (c) uses the sphere map on Mathlib's sphere manifold (not the atlas): for z ∈ (0, 1/2), at every p ∈ S² with xy = z the differential of xy on T_pS² is nonzero (critical values of xy on S² are 0, ±1/2 only: Lagrange (y,x,0) = λ(x,y,z)), so the range plus the horizontal plane is everything; p = (√z, √z, √(1−2z)) witnesses z in the image; `Set.Ioo_infinite`.
Shared tags: rp-smooth-atlas
Doubts: none. Step 4 is independent of the atlas and could be done now.

## Summary

Complete closure probes compiled against the repo on 2026-09-28 (`lake env lean`, scratch files in /tmp/route2probe/, nothing written to the repo): t93J01 (A.lean), t94A04 (A.lean), t93J04 (D.lean), t94A01 (E.lean), t94A03 (F.lean), t94J10, t94J11, t96A04 (G.lean). Each file is a full proof of the frozen statement and can be pasted into Main.lean. For t93J06 and t94A09 the homology half compiled (C.lean); the explicit id ≃ antipodal homotopy from a tangent field (~40 lines) is not yet written.

Groups of shared needs:
- rp-smooth-atlas: t95A04, t96A07 (and the TorusFormTargets analogue torus-quotient-smooth-atlas: t93A06, plus t97A05/t97A06/t98J06 outside this list).
- periodic-stokes-square (Green on a rectangle for a pulled-back exact form): t93A06, t94A10.
- surface-classification / covering-subgroup-correspondence / euler-characteristic-covers: t94J04, t96A01, t95J03.
- polygon-surface-homology / polygon-quotient-identification: t94J09, t95J03, t93J03, t96A02.
- rp-rational-homology: t96A02, t96A06.
- The banked sphere-homology stack (`CoefficientFirstReflection.topIso`, `all_reflections_negative`, `CoefficientSphereAntipodal.antipodal_action`, `SingularHomologyHomotopy`) already closes or nearly closes t93J04, t93J06, t94A09, and the homotopy half of t94A07 and t95J02. That stack is a better starting point than new foundations for these problems.

| id | class | #steps | shared tags |
|---|---|---|---|
| t92J08 | ADAPTER | 4 | manifold-uniform-local-flow |
| t93A06 | FOUNDATION | 7 | torus-quotient-smooth-atlas, periodic-stokes-square |
| t93J01 | DIRECT | 1 (compiled) | none |
| t93J03 | HEAVY | 5 | deck-group-fundamental-group, covering-lifting-criterion, polygon-quotient-identification |
| t93J04 | DIRECT | 2 (compiled) | none |
| t93J06 | DIRECT | 3 (1 compiled) | none |
| t94A01 | DIRECT | 3 (compiled) | none |
| t94A03 | DIRECT | 3 (compiled) | none |
| t94A04 | DIRECT | 1 (compiled) | none |
| t94A07 | ADAPTER | 4 | none |
| t94A08 | FOUNDATION | 3 | projective-affine-chart-homeomorph |
| t94A09 | DIRECT | 1 (reuses t93J06) | none |
| t94A10 | ADAPTER | 3 | periodic-stokes-square |
| t94J04 | HEAVY | 4 | surface-classification, covering-subgroup-correspondence, euler-characteristic-covers |
| t94J09 | HEAVY | 2 | polygon-surface-homology, polygon-cut-and-paste |
| t94J10 | DIRECT | 1 (compiled) | none |
| t94J11 | DIRECT | 1 (compiled) | none |
| t95A04 | FOUNDATION | 5 | rp-smooth-atlas, immersion-from-injective-mfderiv |
| t95J02 | ADAPTER | 5 | none |
| t95J03 | HEAVY | 4 | polygon-surface-homology, euler-characteristic-covers, polygon-quotient-identification, orientation-double-cover |
| t95J06 | HEAVY | 4 | free-circle-action-slice, surface-homology-invariants |
| t96A01 | HEAVY | 4 | van-kampen-amalgamated, surface-classification, covering-subgroup-correspondence, euler-characteristic-covers |
| t96A02 | HEAVY | 4 | lefschetz-fixed-point-theorem, polygon-quotient-identification, rp-rational-homology |
| t96A04 | DIRECT | 2 (compiled) | none |
| t96A06 | HEAVY | 4 | rp-rational-homology, sphere-map-degree, projective-covering-sphere |
| t96A07 | FOUNDATION | 4 | rp-smooth-atlas |

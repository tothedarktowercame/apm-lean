### t00A02 — HEAVY — sorries: 2
Needs:
- `apm_t00A02_bridge_antipodalCover_isCoveringMap`: `IsCoveringMap` for the custom `EqvGen` antipodal quotient `S² → RP²`. The fibre count is already proved (`apm_t00A02_antipodalCover_fiber_card`).
- `apm_t00A02_bridge_global_cover_classification_and_wedge`, which bundles two independent claims:
  - (i) any two path-connected 10-sheeted covers of a compact connected smooth surface with genus-5 integral homology are homeomorphic;
  - (ii) for every `r₀`, there are connected regular and irregular 4-sheeted covers of `RP² ∨ RP²` (glued at `r₀`), packaged as `apm_t00A02_coverWitness … 4 true/false`.

Reuse:
- Mathlib `Topology.IsQuotientMap.isQuotientCoveringMap_of_properlyDiscontinuousSMul`, `IsQuotientCoveringMap.isCoveringMap` (Topology/Covering/Quotient.lean), `Finite.to_properlyDiscontinuousSMul` (Topology/Algebra/ConstMulAction.lean), `Metric.sphere.compactSpace`, the `InvolutiveNeg`/`ContinuousNeg` sphere instances (Analysis/Normed/Group/BallSphere.lean), `IsCoveringMap.eq_of_comp_eq`, and `IsCoveringMap.liftPath`/`exists_path_lifts` (Topology/Homotopy/Lifting.lean).
- In-file: `apm_t00A02_antipodalCover_eq_iff`, `_surjective`, `_fiber_card`.
- Banked: `ConstructionTargets.PointWedgeQuotient` (`Wedge`, `quotientHomeomorphOfRelIff`, `leftOpen/rightOpen_isOpen`) and `ConstructionTargets.PointWedgeRestrictedOpenQuotient` (`quotientMap_isQuotientMap`, `restrictedOpenHomeomorphWedge`), for neighbourhoods of the wedge point.
- Classification of surfaces, or multiplicativity of χ under covers: none found. `ConstructionTargets.Surfaces.eulerCharacteristic` is only a formula on the polygon model.

Route:
1. (antipodal, DIRECT) `instance : MulAction ℤˣ apm_t00A02_Sphere2` (u • x = (u:ℝ) • x), with `ContinuousConstSMul` and `IsCancelSMul` (freeness from x ≠ -x, already argued inside `_fiber_card`).
2. (antipodal) `IsQuotientMap apm_t00A02_antipodalCover` (surjective plus the topology is coinduced by definition), and `∀ e₁ e₂, cover e₁ = cover e₂ ↔ e₁ ∈ orbit ℤˣ e₂` (from `_eq_iff`).
3. (antipodal) `IsCoveringMap apm_t00A02_antipodalCover := (hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul hfG).isCoveringMap`. Closes the first sorry.
4. Split the second bridge into (i) and (ii); pure `And` bookkeeping.
5. (wedge) Gluing lemma: given covers `p : E → X` and `q : E' → Y` with a bijection σ between the fibres over `x₀` and `y₀`, the quotient of `E ⊕ E'` by `e ~ σ e` covers `Wedge x₀ y₀`, and the fibre cardinality is preserved. This is the only nontrivial topology: an evenly covered neighbourhood of the wedge point is the union of two small caps.
6. (wedge) Regular witness: the V₄ = ℤ/2×ℤ/2 cover (a cycle of four S²'s, two over each `RP²`). Build it with step 5 from two copies of (S² ⊔ S² → RP²). Prove it is connected, and prove regularity by exhibiting the four deck homeomorphisms (products of antipodal and swap maps).
7. (wedge) Irregular witness: permutations a = (12), b = (23)(14). Over the first `RP²` the cover has one S² on {1,2} plus RP² copies at 3 and 4; over the second it has S²'s on {2,3} and {1,4}. Prove it is connected.
8. (wedge) Irregularity: a deck map sending sheet 3 to sheet 1 would commute with lifts of the essential loop in the first `RP²`. That loop lifts closed at 3 and open at 1, contradicting uniqueness of lifts (`IsCoveringMap.eq_of_comp_eq`).
9. (classification, HEAVY) Each `E_i` is a compact T2 2-manifold (a finite cover of a compact manifold).
10. (HEAVY) `F` is orientable (from `H₂ ≅ ℤ`) and orientability lifts to covers.
11. (HEAVY) χ(E_i) = 10·χ(F) = −80, with χ read from singular homology.
12. (HEAVY) Classification of closed orientable surfaces by χ, so `E₁ ≃ₜ E₂`.

Size: steps 1–3 are about 3 lemmas. Steps 5–8 are about 6–8 lemmas. Steps 9–12 are a whole surface-classification programme (hundreds of rows). No lighter route exists: the covers are arbitrary topological spaces, so homeomorphism needs classification.
Shared tags: `quotient-by-finite-free-action-covering` (steps 1–3; also t00J01 Klein charts), `wedge-cover-gluing`, `surface-classification`, `euler-characteristic-covering-multiplicativity`, `homology-orientability`
Doubts: none on truth. The bundled second bridge mixes a DIRECT-ish wedge construction with HEAVY classification. Splitting it (step 4) would let steps 1–8 close independently. That split only restructures the bridge lemmas; the frozen `apm_t00a02` statement is not changed.

### t00A03 — HEAVY — sorries: 2
Needs:
- `apm_t00A03_bridge_1`: for a maximal family of pairwise disjoint, nonparallel, essential embedded circles on a compact connected smooth surface with genus-g homology (g ≥ 2), every connected component of the complement is homeomorphic to the open pants `apm_t00a03_Pants`.
- `apm_t00A03_bridge_2`: under the same hypotheses, `n = 3g − 3`.

Reuse:
- In-file point-set lemmas: `apm_t00a03_cut_isOpen`, `_component_isOpen`, `_parallel_of_range_subset_cut/_component`, `_iUnion_components_eq_cut`, `_components_eq_or_disjoint`.
- Banked `ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union/_intersection`, for Euler-characteristic additivity.
- The DAG's plane-arc and transversality rows (568–583, 623–624) do not reach either sorry. The audit's reading is confirmed: the curves are only `Topology.IsEmbedding`, so smooth triangulation work does not apply without tameness.
- Schoenflies, surface classification with boundary, and Baer/Epstein (free homotopy of disjoint simple curves implies an annulus): none found.

Route:
1. 2-D Schoenflies / collar: every embedded circle in a surface has an annulus neighbourhood (it is two-sided because `F` is orientable), so cutting yields a compact surface with boundary.
2. Orientability of `F` from `H₂ ≅ ℤ`, and χ(F) = 2 − 2g read from the homology hypothesis.
3. Epstein: an embedded circle is `apm_t00a03_nullHomotopic` iff it bounds an embedded disk.
4. Baer/Epstein: two disjoint essential embedded circles satisfy `apm_t00a03_parallel` (free homotopy up to reparametrisation) iff they co-bound an embedded annulus.
5. Classification of compact orientable surfaces with boundary (genus, number of boundary components), with χ additivity under cutting along circles.
6. Component analysis (bridge_1): each component is a compact surface of genus h with b boundary circles. If it is not a pants, it contains an essential simple curve that is non-peripheral in that component. By step 4 that curve is not parallel to any curve in the family, which contradicts `hmax` via `apm_t00a03_parallel_of_range_subset_component`. Disks and annuli are excluded by `hessential` and `hnonparallel`. Pants interior ≃ₜ `apm_t00a03_Pants` needs an explicit model homeomorphism.
7. Counting (bridge_2): with P pants, 3P = 2n (each curve borders two sides), and χ(F) = −P = 2 − 2g, so n = 3g − 3. Requires Mayer–Vietoris / χ additivity for singular homology on the cut decomposition.

Size: steps 1, 3, 4 and 5 are each large programmes (Schoenflies alone is a major formalisation). Total: hundreds of rows. No lighter route: the frozen statement is the pants-decomposition theorem for topological curves.
Shared tags: `schoenflies-2d`, `surface-classification`, `simple-curve-homotopy-isotopy` (Baer–Epstein), `homology-orientability`, `euler-characteristic-cut-additivity`, `mayer-vietoris-open-cover` (banked)
Doubts: the statement is true as frozen, because curves are topological and 2-D Schoenflies makes them tame. However, `apm_t00a03_parallel` is free homotopy rather than "co-bound an annulus", and `nullHomotopic` replaces "bounds a disk". Both equivalences (steps 3–4) are deep theorems that the proof must supply. Recommend: do not elect this problem until `surface-classification` exists; it should not be a consumer of the triangulation rows.

### t00J01 — FOUNDATION — sorries: 1
Needs: the single sorry (after the `suffices`) must prove two independent things:
- (A) `apm_t00j01_isThreeManifold (Klein × Circle)`: compact, connected, and locally homeomorphic to open subsets of ℝ³. Also `IsZero (H₃(Klein × Circle; ℤ))`.
- (B) The fold `z ↦ z·exp(2 Im z)` (lift θ + 2 sin θ): regularity at `exp π` and at `1`, and fibre cardinalities 3 and 1. Continuity is already proved; part (b) of the problem (the sphere identity) is already closed.

Reuse:
- In-file: `apm_t00j01_fold_exp`, `_deriv_foldLift`, `_fold_zero`, `_fold_pi`, `_fold_continuous`.
- Mathlib: `Circle.exp` (periodicity, `Circle.exp_arg`, `Circle.coe_exp`), `StrictMonoOn`/`StrictAntiOn` from derivative sign, and `intermediate_value_Icc`.
- Banked `ConstructionTargets.ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union/_intersection` (applied to a zero middle term exactly as in `SphereThreeProductMayerVietoris.sphereThreeProduct_singularH2_isZero`).
- Banked `T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv` and `groupHomologyIsZeroOfModuleHomologyIsZero`; `SolidTorusHomotopyAndHomology.circleModuleHomology_isZero_of_one_lt`; `CircleHomology.circleH1IsoInt`.
- Reflection acting by −1 on H₁ of the circle: `ConstructionTargets.CoefficientFirstReflection.circle_negative` / `integral_circle` (on `euclideanUnitSphere 2`, so it needs transport to `Circle` along `CircleHomology.circleHomeomorphSphereOne`). Klein-bottle homology itself: none found. `t95J02` has a different `KleinRel` with only helper lemmas.

Route:
1. (B) Fibre reduction: `fold z = w` iff z = exp θ with θ ∈ [0, 2π) and θ + 2 sin θ ≡ arg w (mod 2π). On [0, 2π) the lift takes values in [0, 2π), so the congruence is an equality.
2. (B) Root count on [0, 2π): the lift is strictly increasing on [0, 2π/3], decreasing on [2π/3, 4π/3], and increasing on [4π/3, 2π). The critical values 2π/3 + √3 and 4π/3 − √3 are both ≠ π and ≠ 0. That gives exactly three roots of value π (one of them θ = π) and one root of value 0, and no root is critical, which gives `foldRegular` for all real lifts via periodicity. Produce `Nat.card = 3` and `= 1` via an explicit `Fin 3`/`Unique` equivalence.
3. (A) Relation lemma: `EqvGen apm_t00j01_kleinRel (x,y) (x',y') ↔ ∃ m n : ℤ, y' = y + n ∧ x' = (-1)^n·x + m`, by induction on `EqvGen`.
4. (A) Charts: from step 3, the quotient map is open (saturations are unions of affine images) and injective on balls of radius 1/4. Klein charts to open subsets of ℝ², product with arc charts of `Circle`, then a linear homeomorphism to `EuclideanSpace ℝ (Fin 3)`. Compactness and connectedness come from the image of [0,1]² × Circle.
5. (A) `H_k(Klein) = 0` for k ≥ 2. Use the Mayer–Vietoris cover of `Klein` by the images of two horizontal strips (|y| < 0.3 and |y − ½| < 0.3). Each is an annulus ≃ S¹, and the intersection is two annuli. In degree 2 the map H₁(∩) = ℤ² → H₁(U) ⊕ H₁(V) = ℤ² has matrix [[1,1],[1,−1]], because one gluing is x ↦ −x, which acts by −1 on H₁(S¹). The matrix is injective, so H₂ = 0; higher degrees follow from circle vanishing.
6. (A) `H₃(Klein × Circle) = 0`: Mayer–Vietoris with U, V = Klein × (open arc) ≃ Klein, and U∩V ≃ Klein ⊔ Klein. H₃(U) ⊕ H₃(V) = 0 and H₂(U∩V) = 0 by step 5 plus a disjoint-union biproduct.
7. Assemble the conjunction.

Size: (B) is 2–3 elementary real-analysis lemmas (ADAPTER). (A) charts are 2 lemmas. Klein homology (step 5) is the FOUNDATION piece: 3–4 lemmas on banked Mayer–Vietoris plus transport of the banked reflection-degree fact (`circle_negative`) to the annulus cores. About 9 steps total.
Shared tags: `klein-bottle-homology`, `circle-reflection-degree-H1`, `quotient-surface-charts` (shared with t00A02's action quotient), `mayer-vietoris-open-cover` (banked)
Doubts: none. The claim (compact non-orientable 3-manifold with H₃ = 0) is true. Note that H₂(K) = 0 cannot be avoided: without it the H₃ Mayer–Vietoris sequence does not force vanishing (T³ is the counterexample). So some degree −1 (or 2) computation on H₁ is unavoidable.

### t00J02 — HEAVY — sorries: 1
Needs: the single sorry is `hPD : ConstructionTargets.OrientedSurfacePreimageDuality.Producer S` inside `apm_t00J02_bridge_1`. **As stated, this sorry is false, not merely hard.** `Producer S` quantifies over all smooth `f` and embedded `c`. Take `f = id` and `c` the given circle; transversality holds because `mfderiv id` is the identity. Now let ℓ(z) = exp(π·Re z). It factors through the disk (so ℓ_* = 0 on H₁) and is surjective. So `γ = c ∘ ℓ` witnesses `HasNullWindingPreimage` at every point, while `H₂(id) = 𝟙 ≠ 0` since `H₂ ≅ ℤ`.

The flaw is in `EmbeddedCirclePreimage.HasNullWindingPreimage`: it only asks for *some* circle through `x` inside `f⁻¹(range c)`, not a parametrisation of the component. A degree-0 surjective lift therefore always exists.

Probe: `/tmp/routes1/ProducerRefute.lean`, theorem `RouteProbe.not_producer`. It states ¬ `Producer S` under the bridge's own hypotheses plus `H₂(S) ≅ ℤ`. It was compiled against the repo; every part elaborated except one leftover goal `LinearMap.id v + L 0 = v`. The fix for that goal, `rw [map_zero, add_zero]; rfl`, has been written into the file but not recompiled (compile budget). So the entire `Producer` / `DiskBoundedPreimageDuality` / `TransversePreimageDuality` seam cannot close t00J02. What `bridge_1` must actually prove is `H₂(f) = 0`, directly.

Reuse:
- In-file / banked chain that is still valid: `apm_t00j02_exists_component_lift_homologyMap_eq_zero` (each component's lift ℓ into `C` is zero on H₁), `apm_t00j02_mono_homologyMap_of_wrapsHandle`, `IntegerCyclic.mono_of_ne_zero_of_iso`, `CircleHomology.circleH1IsoInt`, `apm_t00j02_degree_eq_zero_of_homologyMap_eq_zero`.
- The Sard modules under `ConstructionTargets/Sard*` (regular values), status unverified for this use.
- Fundamental class / local degree: none found. This is the same missing piece as t98A02 audit item 3.

Route:
1. Delete the `Producer` detour. Restate `bridge_1` as `H₂(f) = 0` from the geometric hypotheses; this does not touch the frozen `apm_t00j02` statement.
2. Fundamental class: `H₂(S) → H₂(S, S∖{y})` is an isomorphism and `H₂(S, S∖{y}) ≅ ℤ` via a chart (tag `manifold-fundamental-class`).
3. Local degree formula: for a regular value `y` of a smooth `f`, `H₂(f)` is multiplication by `Σ_{x∈f⁻¹y} sign det dfₓ` (tag `local-degree-signed-count`).
4. Regular value on `C`: `f⁻¹(C)` is a compact smooth 1-submanifold (preimage theorem, using transversality). A 1-dimensional Sard for `f|: f⁻¹C → C` gives `y ∈ C` regular for `f` (tag `transverse-preimage-submanifold`).
5. Group the signed count by the finitely many components `K` (circles): the contribution of `K` is `±deg(f|K : K → C)`, with the sign constant on `K` because the co-orientation of `C` pulls back continuously.
6. `deg(f|K) = 0`: the circle degree equals the H₁ map, which is 0 by the banked chain (`…_component_lift_homologyMap_eq_zero`). Needs the 1-dimensional count = H₁ degree fact (tag `circle-degree-signed-count`).
7. Conclude `H₂(f) = 0`. Separately, the empty-preimage case (`f` not surjective) needs `H₂(S∖{pt}) = 0`, or can be avoided by picking `y ∈ C \ f(S)`.

Size: steps 2–4 are each substantial and together form the manifold degree theory. Total: a large programme (tens of rows at least). Poincaré duality with cap products is no lighter.
Shared tags: `manifold-fundamental-class` (t98A02), `local-degree-signed-count`, `transverse-preimage-submanifold`, `circle-degree-signed-count`, `sard-regular-value` (partly banked)
Doubts: the frozen statement is true. The current bridge decomposition is unsound because its sorry is refutable, so any loop row targeting `Producer` is wasted. Recommend retiring `OrientedSurfacePreimageDuality.Producer` as a target, or strengthening `HasNullWindingPreimage` to require γ to parametrise the component injectively; that edit is outside the frozen statement.

### t00J07 — FOUNDATION — sorries: 3
Needs:
- `apm_t00J07_bridge_nullhomotopic_attachment_invariants`: for a null-homotopic `f`, X_f = RP² ∪_f D² has π₁ ≃* ℤ/2, H₀ ≅ ℤ, H₁ ≅ ℤ/2, H₂ ≅ ℤ, and H_{≥3} = 0 (X ≃ RP² ∨ S²).
- `apm_t00J07_bridge_essential_attachment_invariants`: for an essential `f`, π₁ is trivial (`ZMod 1`), H₀ ≅ ℤ, H₁ = 0, H₂ ≅ ℤ, and H_{≥3} = 0 (X ≃ S²).
- The main `apm_t00j07` sorry: only the pairing of the two bridges.

Reuse:
- In-file: `apm_t00j07_attach_glue`, `apm_t00j07_center_eqvGen_iff`, `apm_t00j07_basepoint_ne_left`.
- Banked: `ProductionOpenCoverMayerVietoris.productionMayerVietoris_exact_union/_intersection`, `T00A01MayerVietorisAdapters` (`moduleHomologyIsoOfHomotopyEquiv`, `isIso_middle_of_two_exact_of_isZero_ends`, `h0SubspaceInclusionIso`), `SphereHomology`, `SimplyConnectedOpenCover.simplyConnectedSpace_sphere_of_pole`, `DegreeOneHurewiczMap.fundamentalGroupH1Hom` / `CircleHurewiczIsomorphism` (Hurewicz), and `ProjectiveSpaceTopology` (quotient-map facts for `Projectivization`).
- A template for van Kampen, specialised and not generic: `TwiceSpiralFundamentalGroupoidOpenCover` → `TwiceSpiralFundamentalGroupExtraction.gluingFundamentalGroupMulEquivPushout`.
- Mathlib `IsCoveringMap.liftPath` (to compute π₁(RP²) from S² → RP²).
- π₁(RP²), H_*(RP²) and a generic van Kampen: none found.

Route:
1. (DIRECT now) Close the main sorry with `fun f hemb => ⟨bridge_null f hemb, bridge_essential f hemb⟩`.
2. Open cover of X_f: U = X∖{center} and V = image of the open unit disk, with openness via the quotient. U∩V ≃ punctured disk ≃ S¹, V is contractible, and radial pushing gives U ≃ₕ RP² (tag `disk-attachment-punctured-retraction`).
3. RP² model: `Projectivization ℝ (Fin 3 → ℝ)` ≃ₜ S²/± (quotient of nonzero vectors, then normalise). π₁(RP²) ≃* ℤ/2 via the antipodal covering and simple connectivity of S²; the covering step is shared with t00A02 steps 1–3 (tag `rp2-fundamental-group`).
4. H_*(RP²): H₀ = ℤ, H₁ = ℤ/2, H_{≥2} = 0. Use banked Mayer–Vietoris on Möbius band ∪ disk; this needs z ↦ z² to act by ×2 on H₁(S¹), obtained from Hurewicz naturality (tags `rp2-homology`, `circle-power-degree-H1`).
5. Attaching-class dichotomy. Null-homotopic ⇒ `f_* = 0` on π₁ and H₁. Essential ⇒ the free class is nontrivial, so the based class is the generator of ℤ/2, so `f_*` is surjective onto H₁(RP²) = ℤ/2 (Hurewicz is an isomorphism since π₁ is abelian).
6. π₁(X_f) ≅ π₁(RP²)/⟨⟨[f]⟩⟩ via a two-open-set van Kampen with path-connected intersection, then a basepoint transport from the disk center (tag `van-kampen-two-open-cover`). This gives ℤ/2 in case (a) and 1 in case (b).
7. Homology via banked Mayer–Vietoris on (U, V): 0 → H₂(X) → H₁(S¹) = ℤ → H₁(RP²) = ℤ/2 → H₁(X) → 0, plus H₀ and the vanishing degrees. In (a) the map is 0, so H₂ ≅ ℤ and H₁ ≅ ℤ/2. In (b) it is onto, so H₂ ≅ 2ℤ ≅ ℤ and H₁ = 0.

Size: step 1 is one line. Steps 2 and 7 are ADAPTER-sized (about 4 lemmas) on banked Mayer–Vietoris. Steps 3, 4 and 6 are the FOUNDATION pieces: van Kampen is the largest; RP² π₁ and homology are about 3–5 lemmas each. About 7 steps.
Shared tags: `van-kampen-two-open-cover`, `rp2-fundamental-group`, `rp2-homology`, `circle-power-degree-H1`, `disk-attachment-punctured-retraction`, `quotient-by-finite-free-action-covering` (t00A02), `mayer-vietoris-open-cover` (banked)
Doubts: none on truth. The embedding hypothesis is unused: only the homotopy class of `f` matters, so no Schoenflies is needed. Elect step 1 immediately.

### t00J08 — FOUNDATION — sorries: 3
Needs:
- `apm_t00J08_bridge_rank_formula`: if `G ≤ FreeGroup (Fin n)` has finite index and `G ≃* FreeGroup (Fin 7)`, then `6 = G.index * (n - 1)` (the sharp Schreier index formula, specialised to rank 7).
- `apm_t00J08_bridge_subgroup_of_index`: for `0 < n`, `0 < d`, some subgroup of `FreeGroup (Fin n)` has index `d` and is `≃* FreeGroup (Fin (1 + d*(n-1)))`.
- `apm_t00j08` (main): the arithmetic assembly `n ∈ {2,3,4,7}` from the two bridges. Checked by compiling `/tmp/routes1/t00J08_probe.lean` (bridges as sorried hypotheses): forward direction is `(n-1) ∣ 6`, `interval_cases n`; backward direction is `bridgeB` at (2,6), (3,3), (4,2) plus `⊤` for n = 7. `Fin (1 + 6*(2-1))` unifies with `Fin 7` definitionally. So this sorry is DIRECT once the bridges exist.
Reuse:
- Mathlib `Mathlib/GroupTheory/FreeGroup/NielsenSchreier.lean`: `actionGroupoidIsFree`, `endMulEquivSubgroup`, `IsFreeGroupoid.SpanningTree.endIsFree`, `geodesicSubtree`, `IsFreeGroupoid.Generators`. Caveat: `endIsFree` returns `IsFreeGroup (End root)`, which is a Prop, so the explicit generator set `(wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ` is lost. The count needs a Type-valued restatement of the same proof that produces a `FreeGroupBasis` indexed by that complement. The proof body is about 40 lines and can be copied.
- Mathlib `Equiv.ofFreeGroupEquiv : FreeGroup α ≃* FreeGroup β → α ≃ β` (rank invariance, `GroupTheory/FreeGroup/GeneratorEquiv.lean`) and `FreeGroup.freeGroupCongr`.
- Mathlib `Subgroup.index_ker`, `MonoidHom.range_eq_top` (for the witness subgroup's index).
- Problem-local: `apm_t00j08_two_le_of_realizable`. The compiled assembly does not need it.
- `ConstructionTargets/`: nothing (no free-group rank material; `rg FreeGroup` hits only `StatementSurfaceModels.lean`).
Route:
1. `endBasisOfArborescence`: a Type-valued version of `endIsFree`, giving `FreeGroupBasis ((wideSubquiverEquivSetTotal (wideSubquiverSymmetrify T))ᶜ) (End (root' T))`.
2. `card_symmetrify_tree_edges`: for a finite vertex type V, the geodesic arborescence gives exactly `card V - 1` arrows of `Generators`, so the symmetrified tree set has `card V - 1` elements. This needs: exactly one tree arrow into each non-root vertex, and no generator edge in the tree in both orientations (geodesic depths would contradict each other).
3. `card_actionGroupoid_generators`: for `FreeGroup (Fin n)` acting on `FreeGroup (Fin n) ⧸ H`, the generating quiver has `n * H.index` total arrows (one per generator per coset), and the vertex type has `H.index` elements.
4. `schreier_rank_formula`: if `H.FiniteIndex` and `b : FreeGroupBasis ι H`, then `Nat.card ι + H.index = 1 + H.index * n`, stated additively so that it also holds when n = 0. This combines 1–3 with `endMulEquivSubgroup` and `Equiv.ofFreeGroupEquiv`.
5. `bridge_rank_formula`: step 4 with ι = Fin 7, plus omega (the n = 0 case falls out of the additive form).
6. `bridge_subgroup_of_index`: take `H := ker φ`, where `φ : FreeGroup (Fin n) →* Multiplicative (ZMod d)` sends generator 0 to `ofAdd 1` and the others to 1. It is surjective because n > 0, so the index is d. Apply `subgroupIsFreeOfIsFree` or step 1 to get a basis, then step 4 for its size, then `freeGroupCongr` to reach `Fin (1 + d*(n-1))`.
7. Main: paste the compiled assembly from `/tmp/routes1/t00J08_probe.lean`.
Size: steps 1–4 are one coherent Mathlib-level development ("quantitative Nielsen–Schreier"), about 4 lemmas of which step 2 (arborescence edge count) is the fiddliest. Steps 5–7 are short. No topology is involved.
Shared tags: nielsen-schreier-rank-formula
Doubts: none about truth. Two encoding notes. (i) The general formula must not be stated as `rank - 1 = index*(n-1)` in ℕ, because for n = 0 that reads `0 = 1`. Use the additive form in step 4. (ii) The bridge's `6 = G.index * (n - 1)` is correct as frozen, because its hypotheses force n ≥ 2.

### t01A01 — ADAPTER — sorries: 2
Needs:
- `apm_t01A01_bridge_1`: every continuous `g : RP² → RP² \ {q}` is homotopic, inside `RP² \ {q}`, to a constant map. This carries all of the RP² topology.
- `apm_t01a01` (main): (i) from `hfactor` and bridge_1, together with the proved `apm_t01A01_nullhomotopic_of_factor`, `f` is homotopic to a constant. (ii) `FundamentalGroup.map f x γ = 1` for every x and γ, derived from that null-homotopy. Step (i) is two lines. Step (ii) needs one lemma: a null-homotopic map induces the trivial map on π₁ at every basepoint.
Reuse:
- Problem-local, already proved: `apm_t01A01_factor_through_complement`, `apm_t01A01_nullhomotopic_of_factor`.
- `ConstructionTargets.SimplyConnectedOpenCover.simplyConnectedSpace_sphere_of_pole`, which gives S² simply connected: take `E = EuclideanSpace ℝ (Fin 3)` and v a unit vector; `(ℝ∙v)ᗮ` has rank 2.
- Mathlib `IsCoveringMap.existsUnique_continuousMap_lifts` (used in `ConstructionTargets.CoveringLiftRestriction`), with `ConstructionTargets.CircleUniversalCover.circleCover_isCoveringMap` (`Circle.exp : ℝ → Circle`).
- `ConstructionTargets.ComponentRealLiftAssembly.nullhomotopic_of_component_lifts` / `exists_global_lift`: a real lift of a circle-valued map gives a null-homotopy (the formula `Circle.exp ((1-t) F x)`).
- `ConstructionTargets.ProjectiveSpaceTopology` (`quotientMap`, `continuous_quotientMap`) and `ConstructionTargets.RealProjectiveSmoothTarget.sphereProjection` (S² → RP² in the same coinduced topology; its `Space ℝ 2` should be defeq to `apm_t01A01_RP2`, but this is unchecked).
- Mathlib `FundamentalGroupoidFunctor.homotopicMapsNatIso` for (ii). Mathlib `IsOpenQuotientMap.prodMap`, needed to descend homotopies `I × RP²_{≠q} → …` through the quotient.
Route:
1. `projQuot_isOpenQuotientMap`: `Projectivization.mk'` from nonzero vectors of ℝ³ is an open quotient map (saturating an open set by the ℝˣ-action keeps it open). Consequences: its restriction over the open set `RP² \ {q}` and its product with `I` are quotient maps. This is the descent tool for steps 2–4.
2. `punctured_rp2_retract`: for `q = [v]`, write `W := v^⊥`. The map `ρ[w] := [w - (⟪w,v⟫/‖v‖²) v]` goes `RP² \ {[v]} → P(W) ⊆ RP² \ {[v]}`, and `H_t[w] := [w - t(⟪w,v⟫/‖v‖²) v]` is a homotopy from `id` to `ι ∘ ρ` inside `RP² \ {[v]}`. The vector `w - t(...)v` is nonzero and never parallel to v.
3. `rp2_to_line_nullhomotopic`: every continuous `h : RP² → P(W)`, with W a 2-plane, is null-homotopic. Identify `P(W) ≃ₜ Circle` by `[a e₁ + b e₂] ↦ ((a+bi)/|a+bi|)²`. Compose with `sphereProjection` to get `k : S² → Circle`. Lift k to `K : S² → ℝ` (S² is simply connected and locally path connected). Then `K(-x) - K(x) ∈ ℤ` is continuous on connected S², hence a constant c, and c = -c, so c = 0. So K descends to `RP² → ℝ` (step 1), and `nullhomotopic_of_component_lifts` finishes.
4. `bridge_1`: compose steps 2 and 3. `g ≃ ι ∘ ρ ∘ g` by step 2, and `ρ ∘ g ≃ const` by step 3 pushed through `ι`.
5. `fundamentalGroup_map_eq_one_of_homotopic_const`: if `f ≃ const p` then `FundamentalGroup.map f x γ = 1`. Use `homotopicMapsNatIso`: the image is conjugate to the image under the constant map, which is `1`. Then assemble main.
Size: 5 bounded lemmas. Step 1 is the fiddly one (quotient-topology plumbing for the frozen instance); the others are 30–80 lines each. No homology is needed, and π₁(RP²) ≅ ℤ/2 is never computed: the antipodal-constant trick in step 3 replaces it.
Shared tags: projective-quotient-descent, sphere-lift-to-circle (maps from simply connected spaces to Circle lift to ℝ), nullhomotopic-trivial-pi1
Doubts: none. The statement is true as frozen, with π₁ triviality stated at every basepoint, which step 5 handles. The earlier boundary comments ask for π₁(RP²) ≅ ℤ/2 and the circle lifting criterion; this route needs neither.

### t01A02 — FOUNDATION — sorries: 3
Needs:
- `apm_t01A02_bridge_H2map_eq_zero`: a nonsurjective `f : T → T` induces the zero map on integral `H₂` (ModuleCat ℤ singular homology).
- `apm_t01A02_bridge_fixedPoint_of_lift`: if f is nonsurjective and `f = cover ∘ g` for some `g : T → T` (coordinatewise squaring), then f has a fixed point.
- `apm_t01a02` (main): DIRECT once the bridges exist: `intro f hf; exact ⟨apm_t01A02_bridge_H2map_eq_zero f hf, apm_t01A02_bridge_covering_group, apm_t01A02_bridge_fixedPoint_of_lift f hf⟩`. The middle conjunct `bridge_covering_group` is already closed.
Reuse:
- H₂ bridge: `ConstructionTargets.ProductionOpenCoverMayerVietoris` / `productionMayerVietoris_exact_union` and `productionConnecting` (template: `BoundaryTorusIntegralHomologyComplete.boundaryTorusHomology_isZero_of_two_lt`, which is the same argument); `BoundaryTorusMayerVietoris.circleHomology_isZero_of_one_lt`; `SingularHomologyConcrete.singularHomologyIsoOfHomotopyEquiv`; `PointedPuncturedCircleContraction` (`PuncturedCircle`, `puncturedCirclePointedContraction`, `puncturedTorusPointedContraction`, `puncturedTorusHomeomorphNeighborhood`); `IntegralSingularHomologyComparison.singularHomologyModuleIsoOfGroupIso` and `singularHomologyModuleIsZeroOfGroupIsZero` (AddCommGrpCat to ModuleCat ℤ).
- Fixed-point bridge: `CircleUniversalCover.circleCover_isCoveringMap`; `ProductEvenlyCoveredTrivialization.isCoveringMap_productMap` (ℝ² → T); Mathlib `IsCoveringMap.existsUnique_continuousMap_lifts` (ℝ² is contractible); `DegreeFourDiskBoundaryObstruction.normalized_boundary_homotopic_const` (a zero-free map on the closed disk has a null-homotopic normalised boundary loop); `CircleNoncontractible.circle_not_contractible`.
Route (H₂ bridge):
1. WLOG `q = (-1,-1)`. Let `τ x := x * (q⁻¹ * (-1,-1))`, a homeomorphism of the torus group. Then `τ ∘ f` misses `(-1,-1)`, and `H2map (τ ∘ f) = H2map f ≫ H2map τ` with `H2map τ` an iso. So it suffices to treat that one point.
2. `puncturedTorus_H2_isZero`: `H₂(T \ {(-1,-1)}) = 0`. Cover X := T \ {(-1,-1)} by `A = {z₁ ≠ -1}` and `B = {z₂ ≠ -1}`. Their union is X. We have `A ≃ PuncturedCircle × Circle ≃ₕ Circle` (so H₂ = 0) and likewise B, and `A ∩ B ≃ PuncturedCircle²` is contractible (so H₁ = 0). The exact segment `H₂A ⊞ H₂B → H₂X → H₁(A∩B)` then gives H₂X = 0. This copies `boundaryTorusHomology_isZero_of_two_lt` at k = 2.
3. `H2map_eq_zero_of_factor`: f factors as `incl ∘ g'` through X, so `H2map f = H2map g' ≫ H2map incl`, which passes through a zero object and is 0.
Route (fixed-point bridge):
4. `torus_map_integer_lift`: every `h : C(T,T)` has a lift `H : ℝ² → ℝ²` along `(s,t) ↦ (exp s, exp t)` and an integer matrix `A` with `H(x+m) = H(x) + A m` for all `m ∈ ℤ²`. `H(x+eᵢ) - H(x)` is continuous and ℤ²-valued on connected ℝ², hence constant. For `f = cover ∘ g`, the lift of f is `2·G`, so `A_f = 2 B_g`.
5. `planar_bounded_perturbation_surjective`: if `L` is an invertible linear map of ℝ² and `Φ - L` is bounded and continuous, then Φ is surjective. Proof: if Φ misses y, restrict `Φ - y` to a large closed disk. By `normalized_boundary_homotopic_const` its normalised boundary loop is null-homotopic. For large R it is also homotopic, via `(1-s)(Φ - y) + sL`, to `θ ↦ Lθ/|Lθ|`, which is a homeomorphism of the circle. Then `id_Circle` is null-homotopic, contradicting `circle_not_contractible`. This is effectively 2-D Brouwer.
6. `det_eq_zero_of_nonsurjective`: by step 5, if `det A_f ≠ 0` then the lift F is surjective, so f is surjective. Hence `det A_f = 0`.
7. `bridge_fixedPoint`: with `A = 2B` and `det A = 4 det B = 0`, `det(A - I) = 4 det B - 2 tr B + 1 = 1 - 2 tr B` is odd, hence nonzero. Apply step 5 to `Φ(x) = F(x) - x`, which equals `(A - I)x` plus a periodic function, to get x with `F(x) = x`. Then `f(p x) = p x`.
Size: 3 steps for H₂, all pattern-copies of banked MV code. 4 steps for the fixed point, of which step 5 is a real theorem, about 150 lines but assembled from banked pieces. Main: 1 line. About 8 lemmas in total, all bounded. No Lefschetz theorem and no H₁ trace computation is needed.
Shared tags: punctured-torus-H2-vanishing, torus-map-integer-matrix-lift, planar-bounded-perturbation-surjective
Doubts: none. The fixed-point claim is true: the lift gives `A = 2B`, and nonsurjectivity gives `det A = 0`, so the Lefschetz number `det(I - A) = 1 - 2 tr B` is odd. Note that the H₂ bridge is *not* used by the fixed-point route (step 6 uses the covering lift instead of degree), so the two bridges can be worked in parallel.

### t01A03 — HEAVY — sorries: 1
Needs: the single sorry in `apm_t01a03` is a conjunction of three non-retraction claims.
- (c) `¬HasRetraction twoCircles`: already DONE. It is `apm_t01a03_noRetraction_twoCircles twoCircles`; S is connected via `PathConnectedSpace`, so the instance is found automatically.
- (b) `¬HasRetraction wedgeInTorus` for an embedded `S¹ ∨ S¹ → Circle × Circle`: needs π₁(S¹∨S¹) nonabelian and π₁(T²) abelian, then `apm_t01a03_fundamentalGroupMap_injective_of_retraction`. Both hypotheses of `IsTypicalWedge` (embedding, and complement ≃ₜ open disk) are unnecessary.
- (a) `¬HasRetraction middle` for an embedded circle whose complement is homeomorphic to two punctured tori: needs `H1map middle = 0` (a separating curve is null-homologous), after which `apm_t01a03_noRetraction_circle_of_H1_nontrivial` applies (`Nontrivial (H₁ Circle)` is banked via `CircleSingularHomology` / `circleSingularH1Generator_ne_zero`). Deriving `H1map middle = 0` from the frozen hypotheses is the hard part.
Reuse:
- (b): `ConstructionTargets.TwoOpenFreeProductMapping.groupEquivalence` (van Kampen for two opens with simply connected intersection; used in exactly this way in `problems/t00A01/lean/Main.lean`, `apm_t00A01_bridge_fundamentalGroup_coprod`); `PointWedgeQuotient` (`Wedge`, `leftOpen`/`rightOpen`, `quotientHomeomorphOfRelIff`, which identifies the frozen `apm_t01a03_Wedge` with `Wedge (1:Circle) (1:Circle)`); `PointWedgePointedContractionDescent.wedgeHomotopyEquivLeft`; `TorusCircleWedgeOpenCover` (`pointedWedgeHomeomorph`, `wedgeSwap`, `wedgeHomotopyEquivRight`, and the `UModel`/`VModel` pattern to copy with Torus replaced by Circle); `PointedPuncturedCircleContraction.puncturedCirclePointedContraction`; `CircleUniversalCover.circleWindingHom` (+ `_injective`, `_surjective`); `FundamentalGroupProduct.fundamentalGroupProdMulEquiv`; Mathlib `Monoid.Coprod.lift`, `FundamentalGroup.fundamentalGroupMulEquivOfPath`.
- (a): `CircleSingularHomology`, the problem-local `apm_t01a03_noRetraction_circle_of_H1_nontrivial`, and production MV. Nothing banked handles collars or tameness of embedded curves.
Route:
1. (b) `torus_pi1_comm`: `∀ x (a b : FundamentalGroup (Circle × Circle) x), a * b = b * a`, via `fundamentalGroupProdMulEquiv`, change of basepoint to 1, and `circleWindingHom` bijective.
2. (b) `circleWedge_pi1_coprod`: `FundamentalGroup apm_t01a03_Wedge wedgeBase ≃* Monoid.Coprod (FundamentalGroup Circle 1) (FundamentalGroup Circle 1)`. Cover by the images of `{z ≠ -1}` in each summand. Each open is ≃ₕ Circle and the overlap is ≃ₕ a point (wedge contraction descent). Transport along `quotientHomeomorphOfRelIff`. This copies the `TorusCircleWedgeOpenCover` pattern, roughly 3–4 lemmas.
3. (b) `coprod_int_int_not_comm`: the two generators do not commute. Map by `Monoid.Coprod.lift` into `Equiv.Perm (Fin 3)`, sending the generators to a transposition and a 3-cycle.
4. (b) assemble: an injective hom from a noncommutative group into a commutative one is impossible, which gives `¬HasRetraction wedgeInTorus`.
5. (a) `separating_circle_H1_zero`: if `middle : Circle → S` is an embedding in a surface and `S \ range middle ≃ₜ PT ⊔ PT`, then `H1map middle = 0`. Standard proofs need either (i) a collar or annulus neighbourhood of the curve (2-D Schoenflies / tameness of embedded circles in surfaces), after which `[C] = ∂[closure U₁]` or an MV argument applies; or (ii) Alexander/Lefschetz duality. The frozen hypothesis gives only the homeomorphism type of the open complement, not how the components approach C. A π₁ "peripheral loop" argument hits the same collar issue.
6. Main: `⟨(a), (b), apm_t01a03_noRetraction_twoCircles twoCircles⟩`.
Size: (b) is ADAPTER-sized, about 6 lemmas via banked van Kampen. (c) is done. (a) is HEAVY: it needs a tameness/collar programme for embedded circles in 2-manifolds (Jordan–Schoenflies scale, no Mathlib support), or a duality theorem, easily 100+ lemmas. I found no lighter route under the frozen encoding.
Shared tags: circle-wedge-van-kampen, torus-pi1-abelian, surface-curve-collar (Schoenflies-type tameness; also cited by the audit for t00A03 and t98A02)
Doubts: (a) is true, because every embedded circle in a surface is tame. But it is not provable at reasonable cost as frozen, because `IsMiddleCircle` gives only a topological embedding plus the complement's homeomorphism type. Recommend recording (a) as blocked on `surface-curve-collar` and closing (b) now as a partial. (b) does not use `IsTypicalWedge`'s disk-complement hypothesis, so its truth is not in doubt.

### t01A04 — FOUNDATION — sorries: 4
Needs:
- `apm_t01A04_bridge_quotient_maps_are_coverings`: both descended quotient maps `apm_t01a04_circleCoverMap`, `apm_t01a04_torusCoverMap` are `IsCoveringMap` (evenly covered neighbourhoods at the wedge point, where two sheets meet in each total space).
- `apm_t01A04_bridge_piOne_presentation_and_ranges`: generators a,b,c of π₁(T²∨S¹) with the Z²∗Z universal property; two parity characters with the stated values, surjectivity, index-2 kernels, distinct kernels; and range of each induced π₁-map = the corresponding kernel.
- `apm_t01A04_bridge_total_spaces_not_homeomorphic`: CircleCover ≄ TorusCover.
- main `apm_t01a04`: pure assembly of the three bridges plus the already-proved base equations `apm_t01a04_circleCoverMap_base`, `apm_t01a04_torusCoverMap_base` (≈10 lines once bridges exist).
Reuse:
- π₁ of the wedge: `ConstructionTargets.GenericTargetNaturalSourceReconstruction.wedgeFundamentalGroupMulEquiv : FundamentalGroup GenericWedge wedgeBase ≃* Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)` (sorry-free). `GenericWedge = PointWedgeQuotient.Wedge ((1,1)) (1)` uses literally the same generating relation as `apm_t01a04_wedgeRel`, so `PointWedgeQuotient.quotientHomeomorphOfRelIff` gives the homeomorphism with `rfl` on representatives, and `BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph` transports π₁. The exact template is already compiled in problems/t02A03/lean/Main.lean (`apm_t02a03_rel_iff_production`, `apm_t02a03_productionHomeomorph`, `..._base := rfl`, lines ~154–200).
- Coverings: Mathlib `IsCoveringMapOn.of_openPartialHomeomorph` / `IsEvenlyCovered.of_openPartialHomeomorph` (T2 E, T2 X, compact E, local homeomorphism at each fibre point) with `isCoveringMap_iff_isCoveringMapOn_univ`; `Circle.isQuotientCoveringMap_npow 2`, LEMMA-INDEX `apm_t01A02_isCoveringMap_circle_pow_two`.
- Range computation: Mathlib `Topology/Homotopy/Lifting.lean`: `IsCoveringMap.monodromy`, `monodromy_trans_apply`, `monodromy_bijective`, `liftPath`, `eq_liftPath_iff'`, `liftPath_apply_one_eq_of_homotopicRel`, `injective_path_homotopic_map`.
- Algebra: `Monoid.Coprod.lift`, `Monoid.Coprod.hom_ext`, `MonoidHom.ext` on `Multiplicative (ℤ×ℤ)`, `Subgroup.index_ker`.
- Circle loop generator: `ConstructionTargets.CircleUniversalCover`, `CircleMetricFundamentalGroup`, `TorusCircleWedgeConnectorComparison.torusEndMulEquiv/circleEndMulEquiv` (fix the coordinate order: product equivalence, then first/second winding).
Route:
1. `X_homeo : GenericWedge ≃ₜ apm_t01a04_X` and `piOneEquiv : apm_t01a04_piOne ≃* Monoid.Coprod (Multiplicative (ℤ×ℤ)) (Multiplicative ℤ)`, copied from the t02A03 template (mechanical).
2. Wedge π₁ naturality: `piOneEquiv (FundamentalGroup.map torusIncl _ g) = Coprod.inl (torusCoord g)` and the same for the circle inclusion with `Coprod.inr`. Not banked (no `Coprod.inl` lemma exists for the reconstructed equivalence); it has to be extracted from the connector comparison cells `αL`/`αR` in `TorusCircleWedgeFundamentalGroupoidSpan`. This is the riskiest step, because the equivalence was built abstractly (Yoneda-style reconstruction) and may be hard to unwind.
3. Algebra lemma, no topology: a,b,c := piOneEquiv.symm of inl(ofAdd(1,0)), inl(ofAdd(0,1)), inr(ofAdd 1); commutation, closure = ⊤, the ∃! universal property, and φc, φa := (Coprod.lift of parity maps) ∘ piOneEquiv, with their values, surjectivity, index 2 and kernels ≠. (Bounded; one lemma.)
4. `T2Space` and `CompactSpace` for `apm_t01a04_CircleCover`, `apm_t01a04_TorusCover` and `apm_t01a04_X` (finite point identifications of compact Hausdorff spaces), plus `IsLocalHomeomorph` for both maps (open map plus locally injective; at the wedge point, the saturated neighbourhood is two copies of a wedge neighbourhood). Then `IsCoveringMapOn.of_openPartialHomeomorph` closes bridge 1. The same `EqvGen`-quotient evenly-covered argument is what t00A02's bridge is missing.
5. Generic two-sheet monodromy character: for a covering p with a 2-point fibre over x₀ and p e₀ = x₀, `χ_p : FundamentalGroup X x₀ →* Parity`, defined via `monodromy` as a permutation of the fibre (Perm of 2 points is abelian, so anti-hom = hom), with `χ_p.ker = range (FundamentalGroup.map p e₀)`. The range ⊆ ker direction is the lift of a based loop; the ker ⊆ range direction is `liftPath` of a loop whose lift is closed.
6. Evaluate χ_pc and χ_pa on the three loops by explicit lifts: torus loops lift into sheet 0 of CircleCover (closed); the circle loop lifts to a half-circle 1 → exp(πi) (open); and similarly for TorusCover. Via step 2 and `Coprod.hom_ext`, conclude χ_pc = φc and χ_pa = φa. This closes bridge 2.
7. Non-homeomorphism without homology, by cut points. In both spaces the points x with X∖{x} disconnected are exactly the two wedge points: torus minus a point is connected (image under ℝ²→T² of ℝ² minus a countable lattice, `Set.Countable.isPathConnected_compl_of_one_lt_rank`), and a circle minus a point is an arc. A homeomorphism preserves this set, so it restricts to a homeomorphism of the complements. Removing both wedge points leaves 4 components in CircleCover (two punctured tori, two open arcs) and 3 in TorusCover (a twice-punctured torus, two open arcs). This avoids the H₂ computation named in the bridge docstring, which would need Mayer–Vietoris on three-piece quotients.
8. Assemble `apm_t01a04` from bridges 1–3.
Shared tags: eqvgen-quotient-covering-map (with t00A02), two-sheet-monodromy-character (with t97A03), wedge-pi1-inclusion-naturality, cut-point-count-invariant
Doubts: Statement looks true as frozen. Both covers are correct (`sheetPoint 1 = exp π = -1`, squares to 1), and the subgroup identifications match. The only real risk is step 2: if the banked wedge equivalence cannot be evaluated on the concrete inclusion loops, the fallback is to prove the naturality directly by re-running the two-open van Kampen (`TwoOpenFreeProductMapping.basedGroupEquivalence`) with inclusion maps tracked. Even so, this is 8 steps and not a one-probe closure.

### t01A07 — DIRECT — sorries: 1
Needs: the final conjunction of `apm_t01a07`: smoothness, `pointPlus ≠ pointMinus`, `surface ∩ line = {pointPlus, pointMinus}` (all three already proved inside `apm_t01a07_previous_encoding` in the same file), and `apm_t01a07_orientedIntersectionNumber = 0`. The last is a computation: `lineQuartic y = 1 - y^4`, derivative `-4y³`, local signs -1 at y=1 and +1 at y=-1, sum 0.
Reuse: `apm_t01a07_previous_encoding` (same file); Mathlib `hasDerivAt_pow`, `HasDerivAt.const_sub`, `HasDerivAt.deriv`.
Route:
1. Closure probe, already compiled (`lake env lean`, one `unnecessarySimpa` linter warning, no errors) in /tmp/routes1/T01A07Probe.lean. The replacement for the final `sorry` is:
   ```lean
   obtain ⟨hsm, hne, hset, -, -, -⟩ := apm_t01a07_previous_encoding
   refine ⟨hsm, hne, hset, ?_⟩
   have hq : apm_t01a07_lineQuartic = fun y : ℝ => 1 - y ^ 4 := by
     funext y
     simp [apm_t01a07_lineQuartic, apm_t01a07_quartic, apm_t01a07_lineChart]
   have hd : ∀ y : ℝ, deriv apm_t01a07_lineQuartic y = -(4 * y ^ 3) := by
     intro y; rw [hq]
     have := ((hasDerivAt_pow 4 y).const_sub 1).deriv
     simpa using this
   unfold apm_t01a07_orientedIntersectionNumber apm_t01a07_localIntersectionSign
   rw [hd, hd]; norm_num
   ```
   (Change the `simpa` to `simp` to silence the linter.)
Shared tags: none
Doubts: The module docstring still says part (b) is "the orientation-free mod-2 intersection number", but the frozen statement now asserts an integer `orientedIntersectionNumber = 0`, where the number is defined locally as the sum of signs of `deriv (quartic ∘ lineChart)` at y = ±1. That definition does give the correct transverse local signs up to a global orientation flip. However, the theorem is a derivative-sign computation, not a statement about any intersection-theory API. Report this to the grader as a docstring/statement mismatch only; the statement is true and is closed by the probe above.

### t01A08 — HEAVY — sorries: 1
Needs: some p ∈ ℝ² that is a regular value of g := projection ∘ f : X → ℝ² (Fin 2 → ℝ). The model is an arbitrary `I : ModelWithCorners ℝ E H`, E only a finite-dimensional `NormedSpace`, and X is second-countable but not assumed Hausdorff. This is manifold Sard for g, followed by picking a point outside a null set.
Reuse:
- `ConstructionTargets/SardGenuineSmoothManifoldVector.lean`: `T93A04ManifoldWork.null_critical (μ) [IsAddHaarMeasure] (f : M → F) (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) : μ (f '' {y | ¬Surjective (mfderiv …)}) = 0`. It is banked and sorry-free (it closed t93A04/t92J07), but it needs model `𝓘(ℝ,E)` (boundaryless, H = E), `InnerProductSpace E`, and `InnerProductSpace F`.
- `ConstructionTargets/SardGenuineSmoothEuclidean.lean`: `SardGenuineSmoothEuclideanProbe.open_domain_critical_image_null` (open domain, `fderiv`).
- Mathlib: `ContinuousLinearEquiv` to `EuclideanSpace ℝ (Fin n)` (`toEuclideanSpace`-style `ContinuousLinearEquiv.ofFinrankEq`), `Measure.addHaar` image under linear equivalences, `mfderiv_comp`, `ModelWithCorners.Boundaryless`.
Route:
1. Target transport: F := `Fin 2 → ℝ` has the sup norm, not an inner product, so compose with `L : (Fin 2 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)`. Critical sets agree (`mfderiv` of L ∘ g = L ∘ mfderiv g), and L maps null sets to null sets.
2. Boundaryless case (adapter): if `I.Boundaryless`, build a `ChartedSpace (EuclideanSpace ℝ (Fin (finrank E))) X` with `IsManifold 𝓘 ∞` from `I` composed with a linear equivalence, and show `ContMDiff`/`mfderiv` surjectivity are unchanged. Then apply `null_critical`. About 2–3 lemmas, bounded.
3. Boundary/corners case (the large part): for points whose chart image lies in `frontier (range I)`, `mfderiv` is `fderivWithin (range I)`, and the banked Sard covers only open domains with `fderiv`. Two options: (a) a local C^∞ extension across `range I`, which is a Whitney/Seeley-type extension for convex sets with nonempty interior and is not in Mathlib; or (b) re-prove the banked Euclidean Sard for `ContDiffOn ℝ ∞ f s` with s convex with nonempty interior and `fderivWithin`. The banked chain is roughly 170 `Sard*` modules, and its implicit-function induction step assumes open domains. Either option is a programme of tens of rows, not an adapter.
4. Conclude: `volume (g '' crit) = 0`, so `(g '' crit)ᶜ` is nonempty; pick p there. Then every x with f x on the line over p is a regular point.
Shared tags: manifold-sard-general-model, sard-convex-domain (corners part only; possibly shared with t01J04/t96J05, which the DAG lists as Sard uptake)
Doubts: The statement is true as frozen (Sard holds for manifolds with corners). But the frozen generality `ModelWithCorners ℝ E H` with arbitrary H goes beyond the source's boundaryless "smooth manifold", and that generality is the only thing that makes this HEAVY rather than ADAPTER: steps 1, 2 and 4 would close the boundaryless case. There is no lighter route for the corners case within the frozen statement. (I have not checked whether Mathlib's current `ModelWithCorners` guarantees convex range; option (b) assumes it does.)

### t01J01 — HEAVY — sorries: 3
Needs:
- `apm_t01J01_bridge_separates_of_nullHomologous`: an embedded (merely topological) circle γ in a compact connected smooth surface S with genus-2 homology and γ_* = 0 on H₁ has disconnected complement.
- `apm_t01J01_bridge_annulus_of_separating`: two disjoint, separating, non-null-homotopic embedded circles in such an S cobound a subset A ≃ₜ S¹ × [0,1] with `frontier A = range γ₁ ∪ range γ₂`.
- main `apm_t01j01`: two applications of bridge 1, then bridge 2. This is DIRECT once the bridges exist (about 3 lines).
Reuse: only the witness-interface lemmas in Main (`apm_t01j01_range_isClosed`, `..._isCompact_of_isAnnulusBetween`, `..._ranges_subset_of_isAnnulusBetween`, `..._ne_univ_of_isAnnulusBetween`). `OrientedSurfacePreimageDuality` / `DiskBoundedPreimageDuality` are interfaces for smooth, transverse preimages (t00J02) and do not apply to topological curves. Mathlib has no Jordan curve theorem, no Schoenflies theorem, no surface classification and no intersection pairing. Nothing banked supplies either bridge.
Route (the programme; each item is itself multi-row):
1. Tameness: every embedded circle in a topological 2-manifold has a closed neighbourhood homeomorphic to an annulus or a Möbius band (2-D Schoenflies, applied chartwise). Every later step needs this, because the curves are only `IsEmbedding`.
2. Two-sidedness from orientability (H₂ ≅ ℤ gives the orientation, which itself needs a fundamental-class/orientation-from-top-homology argument); so the neighbourhood is an annulus.
3. Separation (bridge 1): if S∖γ were connected, a loop crossing the collar once has mod-2 intersection 1 with γ. Build the mod-2 intersection pairing on H₁ (or Mayer–Vietoris on S = collar ∪ (S∖γ)) and show a null-homologous γ has pairing 0, a contradiction.
4. Cutting: S∖(open collar of γ₁) is two compact surfaces with one boundary circle each. Genus bookkeeping via Mayer–Vietoris on homology, with γ₁ essential, shows each is a one-holed torus.
5. Classification within a one-holed torus T′ that contains γ₂: a separating circle in T′ either bounds a disk (excluded because γ₂ is not null-homotopic in S) or cobounds an annulus with ∂T′ = γ₁. This needs classification of compact surfaces with boundary, or at least of planar pieces (an annulus recognition theorem).
6. Frontier bookkeeping: `frontier A = range γ₁ ∪ range γ₂` needs invariance of domain in dimension 2, so that the manifold interior of A is its topological interior in S.
Rough size: 2-D Schoenflies alone is a major formalisation (hundreds of rows at the observed pace); classification of surfaces with boundary is comparable. No lighter route exists within the frozen statement: it quantifies over topological embeddings, so smooth transversality shortcuts are unavailable.
Shared tags: surface-schoenflies-tameness, surface-mod2-intersection-pairing, surface-cut-and-classify, orientation-from-top-homology, invariance-of-domain-dim2 (overlaps with t00A03/t99J03 surface rows, which the audit already flags as needing Schoenflies)
Doubts: The claim is true as frozen: bridge 1 is the standard homology/separation fact, and bridge 2 follows from classifying the one-holed torus. The encoding's genus-2 surface is "smooth manifold with genus-2 homology", which is enough (orientability from H₂ ≅ ℤ, genus from H₁ ≅ ℤ⁴). Frontier equality for a closed annulus in S holds by invariance of domain. The difficulty is that curves are only topologically embedded, not that the statement is false. Recommend not electing this until surface-classification foundations exist, per the DAG's own "late FOUNDATION" note.

### t02A02 — FOUNDATION — sorries: 1
Needs: `apm_t02a02 : Nonempty (apm_t02a02_F ≃ₜ Surface false 2)`, i.e. an actual homeomorphism from the octagon quotient (word `aabcc⁻¹d⁻¹bd⁻¹`, EqvGen of `apm_t02a02_gluingRel` on `Disk`) to the square quotient `aabb` (`ConstructionTargets.Surfaces.Surface false 2`). No invariant shortcut exists: the conclusion is a homeomorphism, so the Euler-characteristic/orientability data already compiled in `apm_t02a02_previous_encoding` does not help.
Reuse: `ConstructionTargets.Surfaces` (`Disk`, `edgePoint`, `SurfaceRel`, `Surface`, `continuous_surfaceQuotient`, `surjective_surfaceQuotient`); Mathlib `Continuous.homeoOfEquivCompactToT2`, `Quotient.lift`/`Continuous.quotient_lift`. No polygon cut-and-paste, fold, or T2-quotient infrastructure found (rg over ConstructionTargets for fold/cancel/polygon homeomorph/T2Space of quotients: none).
Route:
1. `polygon_quotient_t2 : T2Space (Quotient (EqvGen.setoid R))` for any edge-pairing relation R on `Disk` built from `edgePoint` (closed relation on a compact Hausdorff space); instantiate for `apm_t02a02_F` and `Surface false 2`. Compactness is free (image of compact `Disk`).
2. `edgeclass_characterisation`: for an edge-pairing word, the EqvGen class of an interior point is a singleton, of an edge-interior point is its pair, of a vertex is the vertex class (here `apm_t02a02_vertexClass`, 3 classes; for `aabb`, 1 class). This is the generic "quotient classes of a polygon word" lemma both injectivity proofs need.
3. `apm_t02a02_cutPasteMap : C(Disk, Surface false 2)` — explicit piecewise map (cut the octagon along diagonals, fold the adjacent `cc⁻¹`, reassemble into the square `aabb`), with `∀ x y, gluingRel x y → Φ x = Φ y`.
4. `apm_t02a02_bijective`: the descended map `apm_t02a02_F → Surface false 2` is bijective (uses step 2 on both sides; the piecewise definition must match boundary arcs exactly).
5. Assemble with `Continuous.homeoOfEquivCompactToT2`.
Size: steps 1–2 are reusable foundation (each a sizeable lemma over `Relation.EqvGen`); steps 3–4 are a concrete but fiddly piecewise-geometry proof (probably the bulk). Better long-term: a small library of elementary word moves (`fold` of an adjacent `xx⁻¹`, cyclic rotation, cut-and-paste along one diagonal) each as a homeomorphism of polygon quotients, then compose — reusable for t98A01 and other polygon-word problems.
Shared tags: polygon-quotient-t2, polygon-word-quotient-classes, polygon-cut-paste-homeomorph
Doubts: none on truth. I checked the encoding: equal signs glue `t ↔ t`, opposite signs `t ↔ 1-t`, matching `SurfaceRel false 2` (edge 2j ↔ 2j+1, `t ↔ t`, i.e. `aabb`); χ = 3−4+1 = 0 and the surface is non-orientable, so the target (the Klein bottle) is correct.

### t02A03 — FOUNDATION — sorries: 1
Needs: the one `sorry` in `apm_t02a03` is an 8-way conjunction. Conjuncts 3–8 (π₁ of the torus and of Y, H₀/H₁/H₂/H_{≥3} of Y) are *already proved* in the same file as `apm_t02a03_previous_encoding`. What is left:
 (a) `Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_X apm_t02a03_Torus)`: (closed unit disk in ℂ minus 0) × Circle ≃ₕ Circle × Circle;
 (b) `Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY apm_t02a03_Y)`: (closed 1/4-neighbourhood W in ℝ³ of the planar figure-eight made of two unit circles tangent at 0) minus the left circle C ≃ₕ torus ∨ circle.
Reuse: `apm_t02a03_previous_encoding` (in Main.lean, sorry-free); `ConstructionTargets.PuncturedNormedSpaceRadialEquivalence` (`radialNormalize`, `puncturedRadialHomotopy`, `unitSphereHomotopyEquivPuncturedSpace`, `…ProductHomotopyEquiv…Product` via `HomotopyEquiv.prodCongr`); the same pattern for a disk in `T02A06DiskRadialComparison.sphereHomotopyEquivPuncturedOpenDisk`; `SolidTorusHomotopyAndHomology` (explicit contraction to a core, as a template). Nothing found for (b): no ℝ³ tube-neighbourhood retractions and no gluing lemma for homotopy equivalences.
Route:
0. (verified by compile, /tmp/routes1/t02A03probe.lean) With (a) and (b) as named sorries, `exact ⟨probe_X, probe_Y, apm_t02a03_previous_encoding⟩` closes the main theorem, leaving only those two sorries.
1. `closedPuncturedDisk_homotopyEquiv_circle : {p : closedBall (0:ℂ) 1 // p.1 ≠ 0} ≃ₕ Circle`: the radial homotopy `x ↦ ((1-t)/‖x‖ + t)•x` from `PuncturedNormedSpaceRadialEquivalence` has norm `(1-t)+t‖x‖ ≤ 1`, so it stays in the disk; `Circle` is `sphere 0 1` in ℂ. Then take the product with `Circle` via `HomotopyEquiv.prodCongr`, plus the homeomorphism between the subtype of a product and a product of subtypes. Closes (a). ADAPTER-sized, about 1–2 lemmas.
2. `geomY_to_Y`, `Y_to_geomY`: explicit maps for (b). Into geometricY: send the torus to the 1/8-tube around C and send the circle to R lifted to height z = 1/8 (this stays in W and misses C; the two meet at (0,0,1/8)). Out of geometricY: a continuous map to T ∨ S¹. The spine is singular at the tangency point, so nearest-point retraction does not work, and a piecewise formula is needed.
3. The two homotopies to the identity. This is where most of the work is: the concrete 3-dimensional deformation must avoid C and stay inside the `infDist ≤ 1/4` set near the tangency.
   Alternative for 2–3: decompose W∖C = (V_L∖C) ∪ (V_R∖C) over a ball B. Use V_L∖C ≃ₕ T² (the step-1 pattern in tube coordinates), V_R∖(arc) ≃ₕ S¹∨S¹ and B∖arc ≃ₕ S¹, then apply a gluing lemma for homotopy equivalences along closed cofibrations. That lemma does not exist in the library and is itself a foundation.
Size: (a) is small. (b) is a single theorem but a large one: an explicit ℝ³ deformation retraction with `Metric.infDist`-defined sets and a tangency singularity, plausibly hundreds of lines. It could equally be called HEAVY. The lighter part (a) can be banked now.
Shared tags: explicit-r3-tube-deformation-retraction, homotopy-equiv-gluing-lemma
Doubts: I believe (b) is true. W is a union of two solid tori (tube radius 1/4 < curvature radius 1) meeting in a ball around the tangency point. C crosses that ball as an unknotted arc, and van Kampen gives (ℤ×ℤ)∗ℤ. The tangency of the two circles at 0 is an unusual choice of spine and makes step 2 harder than a transversal wedge would. Nothing is wrong with the statement.

### t02A04 — HEAVY — sorries: 3
Needs:
 - `apm_t02A04_bridge_1`: X = (D²×S¹) ∪_{z↦(z,z²)} D² has rational singular homology H₀ ≅ ℚ and H_k = 0 for k > 0.
 - `apm_t02A04_bridge_2`: from that hypothesis, every continuous f : X → X has a fixed point. This is the Lefschetz fixed-point theorem specialised to X.
 - `apm_t02a04` (main): follows immediately, `fun f hf => apm_t02A04_bridge_2 apm_t02A04_bridge_1 f hf`. This is DIRECT once the bridges exist.
Reuse:
 - For bridge_1: `ProductionOpenCoverMayerVietoris` (integral, open cover) and its `Coefficient*` R-module ports (needed because the statement uses `ModuleCat ℚ`); `SolidTorusHomotopyAndHomology` (`solidTorusHomotopyEquivCircle`, solid-torus H_k); `T00A01MayerVietorisAdapters.moduleHomologyIsoOfHomotopyEquiv`; `SolidTorusGluingOpenCover` / `TwiceSpiralGluingHomology` / `T96A03DegreeTwoMayerVietoris` as templates (open cover of a quotient, radial band retractions, a degree-2 connecting map); the local `apm_t02a04_gluedDesc` universal property.
 - For bridge_2: `ConstructionTargets.RationalLefschetz` gives only *definitions* (`HasLefschetzNumber`); no fixed-point theorem. Mathlib has no topological Lefschetz theorem.
Route:
1. `X_openCover`: U = X minus the centre of the attached disk, V = the image of the open disk, both open, U ∪ V = X, U ∩ V ≃ₕ annulus ≃ₕ S¹.
2. `U_homotopyEquiv_solidTorus`: radial push-off of the punctured disk onto its boundary, descended through the quotient. The pattern is `SolidTorusGluingOpenCover.annularBandHomotopyEquiv`.
3. `H1_inclusion_is_two`: the map H₁(U∩V; ℚ) → H₁(U; ℚ) ≅ H₁(S¹; ℚ) is multiplication by 2 (the attaching circle has second coordinate z²). It is therefore an isomorphism over ℚ.
4. `bridge_1`: ℚ-coefficient MV assembly: H₀ = ℚ, H₁ = coker(×2) = 0, H₂ = ker(×2) = 0, and H_k = 0 for k ≥ 3.
5. `bridge_2`: needs Lefschetz for X, which is the HEAVY part. Either (i) prove X is a compact polyhedron (an explicit triangulation of the quotient) and prove Lefschetz for finite simplicial complexes (simplicial approximation, simplicial-to-singular comparison, Hopf trace formula), or (ii) prove Lefschetz for compact ENRs (a neighbourhood retract of ℝⁿ, then reduce to polyhedra). Either way this is a programme of many dozens to hundreds of rows. I found no lighter route: the fixed-point property is not a homotopy invariant, so the homotopy equivalence X ≃ RP² does not transfer it, and a covering-space/degree argument on the double cover of X is no smaller.
Size: steps 1–4 are FOUNDATION, and a template exists (t01J03 twice-spiral and t96A03 gluings), about 4 rows with the ℚ-port. Step 5 is a HEAVY programme: `lefschetz-fixed-point-compact-polyhedron`.
Shared tags: lefschetz-fixed-point-compact-polyhedron, cell-attachment-open-cover-mv, coefficient-q-mayer-vietoris
Doubts: none on truth. The curve z ↦ (z, z²) is simple and has longitude degree 2, so π₁X = ℤ/2 and X ≃ RP². X is a compact polyhedron, so Lefschetz applies with L(f) = 1. `bridge_2` also holds as stated, because its conclusion is true unconditionally.

### t02A05 — ADAPTER (mechanically), but FROZEN STATEMENT APPEARS FALSE — sorries: 2
Needs:
 - `apm_t02A05_bridge_1`: for every centre c, `∫_{sphere c 1} orientedCoefficient ∂μH[2] = 44π/15 + 4π((c₀-1)²+(c₁-2)²)`.
 - `apm_t02a05` (main): immediate from bridge_1 + the compiled `apm_t02a05_quadratic_minimum`.
Reuse (much of this is already banked):
 - `IntrinsicSphereFourthMoments.unitFlux_moment : ∫ x : Sphere 2, x₀(x₀+c₀-1)³ + x₁(x₁+c₁-2)³ + x₂(x₂+c₂-3) ∂μH[2] = mass 2 * (11/15 + (c₀-1)² + (c₁-2)²)`.
 - `IntrinsicSphereFinite` (integrability).
 - `IntrinsicSphereSecondMoments.integral_isometry` / `sphereIsometry` (transport along isometries).
 - `SphereCapNullEquatorMeasureAssembly.sphere_two_measure : μH[2](sphere 0 1) = 2·∫⁻_{ball 0 1 ⊂ E²} 1/√(1-‖x‖²) ∂μH[2]`.
 - `SphereCapC1GraphAreaComparison.subtype_measure`.
 - Mathlib: `Submodule.orthogonalProjection_orthogonal_val` / `orthogonalProjection_singleton` for P eᵢ = eᵢ − nᵢ n, and `IsometryEquiv.vaddConst` for the translation.
Route (to the *true* formula):
1. `orientedCoefficient_eq_flux`: for q on the sphere with n = q − c, `orientedCoefficient ω c q = F(q)·n`, where F = ((x₀-1)³, (x₁-2)³, x₂-3). This is pointwise algebra: P eⱼ × P eₖ = det(n, eⱼ, eₖ)·n, so the sum is ‖n‖²·(F·n) = F·n. I checked this by hand.
2. `integral_translate`: transport the subtype integral from `sphere c 1` to `Sphere 2` along x ↦ x − c. Here the integrand becomes exactly `unitFlux c`. Use `integral_isometry`-style transport with a translation isometry.
3. `mass_two_eq`: evaluate `mass 2`, which requires μH[2] on `EuclideanSpace ℝ (Fin 2)` = k·volume and then ∫_{unit disk} (1-‖x‖²)^{-1/2} = 2π. This gives mass 2 = 4πk.
4. Assemble.
Shared tags: euclidean-hausdorff-normalisation (i.e. the isodiametric constant). The same issue affects `t01J06`, which also integrates against `μH[2]` on a sphere.
Doubts: **the frozen statement looks FALSE.** Mathlib's `μH[d]` is unnormalised: it is the sum of `diam^d` with no ω_d/2^d factor (see the Mathlib Hausdorff.lean docstring; only `hausdorffMeasure_pi_real`, for the *sup* metric, equals Lebesgue). On Euclidean ℝ², unnormalised H² = (4/π)·Lebesgue (isodiametric constant π/4), so k = 4/π and `mass 2` = μH[2](S²) = 16, not 4π. By the banked `unitFlux_moment` the integral is then 16·(11/15 + (c₀-1)² + (c₁-2)²) = 176/15 + 16(…). The first conjunct (≥ 44π/15 ≈ 9.215) is still true, since 176/15 ≈ 11.73. The second conjunct (`= 44π/15 ↔ c₀=1 ∧ c₁=2`) fails at c = (1,2,0): the right side holds, the left side does not. `bridge_1` is false for every c. The whole problem reduces to whether `mass 2 = 4π`, and `EuclideanAndSupUnitBallVolumes.md` already describes the normalisation as "remaining downstream".
A disproof needs only k > 1. That requires a weak planar isodiametric bound: a set of diameter r lies in the intersection of four width-r strips (a regular octagon of area 2(√2−1)r² ≈ 0.83 r²), so μH[2] ≥ volume/0.83 on E², plus Haar uniqueness to write μH[2] = k·volume. Not compiled. The grader should re-examine the normalisation (e.g. state it with `(π/4)•μH[2]` or with `Measure.toSphere`) before any loop spends rows on bridge_1.

### t03J02 — HEAVY — sorries: 2
Needs:
- `apm_t03J02_bridge_1`: π₁ of the quotient `T₁ ⊔ T₂ / (j₁ z ~ j₂ z)` at `j₁ z₀` is ≃* the 4-generator, 2-commutator presentation (ℤ² * ℤ²), for arbitrary *topological* embeddings `j₁ j₂` that are null-homotopic.
- `apm_t03J02_bridge_2`: integral singular homology of the same quotient: H₀ ≅ ℤ, H₁ ≅ ℤ⁴, H₂ ≅ ℤ³, Hₖ = 0 for k ≥ 3.
- (`apm_t03j02` itself is already closed from the two bridges.)
Reuse:
- Quotient layer in Main: `apm_t03J02_gluedDesc`, `apm_t03J02_gluedDescEquiv`, `apm_t03J02_glue_eq` (continuous pushout eliminator).
- Open-cover MV: `ConstructionTargets.ProductionOpenCoverMayerVietoris` (`productionMayerVietoris_exact_pieces`, `productionMayerVietoris_exact_union`, `productionConnecting`); the complete worked template is `TorusCircleWedgeMayerVietoris.genericWedge_complete_module_homology` (incl. its degree-0 handling via `openCoverH0IsoOfCoordinates`).
- Torus homology: `BoundaryTorusIntegralHomologyComplete` (H₁ ≅ Fin 2 → ℤ, H₂ ≅ ℤ, vanishing ≥ 3, for `Circle × Sphere 1`; its README says H₀ is a separate seam), circle: `CircleSingularHomology.circleSingularH1IsoInt`.
- Torus π₁: `BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph`, `boundaryTorusFundamentalGroupMulEquivFinTwo`.
- van Kampen pieces: `TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence`, `FundamentalGroupoidOpenCoverSubdivision`, and the closed `t01J03` as the only worked specialisation of pseudopushout → group pushout (`Monoid.PushoutI`, cf. `TwiceSpiralFundamentalGroupPushout`).
- Nothing on Jordan/Schoenflies anywhere in ConstructionTargets or Mathlib (rg for schoenflies/jordan curve/brouwer/poincare-miranda: no hits).
Route:
1. `embedded-circle-collar-surface`: for a topological embedding `j : Circle → Circle × Circle`, ∃ open `N ⊇ range j` and a homeomorphism `N ≃ₜ Circle × Ioo (-1) 1` sending `j z` to `(z, 0)`. (Null-homotopic ⇒ lifts to a simple closed curve in ℝ²; Jordan–Schoenflies in ℝ² gives a disk and an annular collar; translates of the disk are disjoint, so it projects injectively.) This is the Schoenflies theorem; not in Mathlib, a large programme on its own.
2. Open cover of the quotient: `A = q(T₁ ⊔ N₂)`, `B = q(N₁ ⊔ T₂)` are open, `A ∪ B = univ`, and `A ≃ₕ T₁`, `B ≃ₕ T₂`, `A ∩ B ≃ₕ Circle` (collar deformation retractions descended through `apm_t03J02_gluedDesc`).
3. `van-kampen-open-cover` specialised: for the path-connected open cover in step 2 with basepoint in `A ∩ B`, `π₁ X ≃* Monoid.PushoutI` of `π₁(A∩B) → π₁ A, π₁ B`; both legs are trivial because `j₁`, `j₂` are null-homotopic.
4. Algebra: the pushout of `ℤ² ← ℤ → ℤ²` with trivial legs is ≃* `apm_t03J02_freeProductZ2Z2` (PresentedGroup with 4 generators, 2 commutators). Closes bridge_1.
5. MV on the same cover, following the `TorusCircleWedgeMayerVietoris` template: the H₁(A∩B) → H₁(A) ⊕ H₁(B) map is 0 (null-homotopy + homotopy invariance), so H₂ ≅ ℤ² ⊕ ker = ℤ³, H₁ ≅ coker = ℤ⁴, H₀ ≅ ℤ, Hₖ = 0 for k ≥ 3. Closes bridge_2.
Shared tags: embedded-circle-collar-surface (jordan-schoenflies), van-kampen-open-cover, mayer-vietoris-open-cover (exists), torus-fundamental-group, connected-h0
Doubts: The frozen claim is true, but only because of Schoenflies: `IsEmbedding` admits arbitrary topological curves, so no collar is given, and without one neither excision nor van Kampen applies to the closed gluing. The source problem presumably meant tame curves. Steps 2–5 are bounded (about 10–20 rows, templates exist); step 1 dominates, and I know of no route that avoids it. The DAG's own STOP entry for t03J02 (lines ~703, 753) records the same collar/cofibration blocker.

### t03J03 — HEAVY — sorries: 4
Needs:
- `apm_t03J03_bridge_1`: seven explicit connected 2-fold covers of `Surface false 3`, indexed by nonzero characters `Fin 3 → ZMod 2`. Every connected double cover is equivalent over N₃ to exactly one of them, and the total space is ≃ₜ `Surface true 2` for the all-ones character and ≃ₜ `Surface false 4` otherwise.
- `apm_t03J03_bridge_2`: every disconnected 2-fold cover of N₃ is equivalent over N₃ to `Sum.elim id id : N₃ ⊕ N₃ → N₃`.
- `apm_t03J03_bridge_3`: every embedded closed cylinder `Circle × Icc 0 1 → N₃` lifts to every 2-fold cover whose total space is ≃ₜ some `Surface true g`.
- main `apm_t03j03`: after the existing `refine`, only `exact ⟨apm_t03J03_bridge_1, apm_t03J03_bridge_2, apm_t03J03_bridge_3⟩` (closable now; it only moves the obligation into the bridges).
Reuse:
- In Main: `apm_t03J03_exists_cylinderLift_of_range_le` (Mathlib lifting criterion, packaged), Euler/character-count lemmas.
- `ConstructionTargets.Surfaces` (`Surface`, `surfaceQuotient`, `continuous_surfaceQuotient`, `surjective_surfaceQuotient`; no topology facts beyond these).
- `ConstructionTargets.LiteralPullbackCover` (`Pullback`, `isCoveringMap`, `fiber_card`, `sheet_card`), for pulling a cover back to the disk.
- Mathlib: `IsCoveringMap.isLocalHomeomorph`, `IsCoveringMap.eq_of_comp_eq`, `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, `IsEvenlyCovered.restrictPreimage`, `Homeomorph.homeomorphOfContinuousOpen`.
- No π₁ of any polygon surface, no cover classification, no surface homeomorphism/classification, no orientation theory for topological surfaces (FundamentalGroupConcrete.md lists all of these as unchecked).
Route:
1. (main) Close the main sorry with the three bridges (1 line).
2. (bridge_2) `Surface false 3` is connected and locally connected: image of the closed disk; locally connected because it is a quotient of a locally connected space.
3. (bridge_2) For a covering over a connected, locally connected base, and clopen `A ⊆ E`, `x ↦ Nat.card (A ∩ p⁻¹{x})` is constant.
4. (bridge_2) Fibre count 2 plus `E` disconnected ⇒ a clopen `A` with count 1 on `A` and on `Aᶜ` ⇒ `p|A`, `p|Aᶜ` are bijective open maps, hence homeomorphisms. Assemble `E ≃ₜ N₃ ⊕ N₃` over N₃. Closes bridge_2 (steps 2–4 are ADAPTER-sized).
5. (bridge_1) `covering-trivial-over-disk`: every 2-fold cover of the closed disk is ≃ `Disk × Fin 2` (simply connected + lifting criterion).
6. (bridge_1) `polygon-cover-descent`: pull back along `surfaceQuotient false 3`, so the cover is a quotient of `Disk × Fin 2` determined by a swap label ε ∈ (ZMod 2)³ on the three edge pairs. ε is constant along each edge (edges are connected), and equal labels give equivalent covers.
7. (bridge_1) Construct `reps ε` as that quotient: prove covering map, fibre card 2, connected iff ε ≠ 0, and ε is recoverable (so equivalence is unique).
8. (bridge_1) `polygon-cut-and-paste-homeomorph`: explicit homeomorphisms from the two-hexagon quotients to the standard octagon quotients, for ε = (1,1,1) → `Surface true 2` and ε = (1,0,0), (1,1,0) → `Surface false 4`. The other four characters follow by the rotation symmetry of the `aabbcc` polygon, which also has to be built. In Lean this is the bulk of bridge_1.
9. (bridge_3) `polygon-surface-homology`: `Surface false 4` and `N₃ ⊕ N₃` are not ≃ₜ any `Surface true g` (N₃ ⊕ N₃ is disconnected; N₄ has 2-torsion in H₁, Σ_g does not). So an orientable 2-fold cover is `reps (1,1,1)`.
10. (bridge_3) `covering-monodromy-character`: the (1,1,1) cover's monodromy along a loop is the orientation character of the loop's class, which gives the range inclusion needed by the banked lift lemma.
11. (bridge_3) `surface-local-homology-orientation` + `invariance-of-domain-dim2`: the core loop of a *topologically* embedded closed annulus in N₃ has orientation character 0 (two-sidedness). Then apply `apm_t03J03_exists_cylinderLift_of_range_le` (after `PathConnectedSpace`/`LocPathConnectedSpace` instances for `Circle × Icc 0 1`).
Shared tags: covering-trivial-over-disk, polygon-cover-descent, polygon-cut-and-paste-homeomorph, polygon-surface-homology, covering-monodromy-character, surface-local-homology-orientation, invariance-of-domain-dim2
Doubts: All three bridges are true as frozen. Size: bridge_2 is 3 lemmas and can be elected on its own now. Bridge_1 is dominated by step 8 (explicit piecewise homeomorphisms between polygon quotients, one of the heaviest kinds of Lean work). Bridge_3 needs orientation theory for topological (non-smooth) surfaces, and no row anywhere provides it. A lighter route to bridge_1's identification step would be a classification-of-surfaces theorem, which is heavier still.

### t91A02 — HEAVY — sorries: 1
Needs:
- `apm_t91a02`: no covering map `Surface false 16 → Surface false 8` with every fibre of cardinality `sheets > 0`. The intended proof is χ(E) = d·χ(B): −14 = −6d has no integer solution.
Reuse:
- `ConstructionTargets.Surfaces` (`Surface`, `eulerCharacteristic`, which is only the number `2 − g`, not a homology invariant).
- `ConstructionTargets.CoveringDegree.IsKSheetedCover`. `CoveringTransferChain.transfer` / `transfer_projection` (chain-level transfer with p_* ∘ τ = d) gives only p_*τ = d, which does not force multiplicativity of χ.
- `LiteralPullbackCover` (pulling the cover back to the disk).
- Nothing computes the homology or π₁ of any `Surface false g`.
Route:
1. `covering-trivial-over-disk`: a d-sheeted cover of the closed disk is ≃ `Disk × Fin d`.
2. `polygon-cover-descent`: a d-sheeted cover of `Surface false 8` is the quotient of `Disk × Fin d` by a permutation-labelled gluing of the 8 edge pairs. It is a polygon complex with V = d vertices, E = 8d edges and F = d faces.
3. `polygon-complex-euler-characteristic`: for a finite polygon complex (quotient of finitely many disks by boundary-edge pairings), Σ(−1)ⁱ rank Hᵢ(·; ℚ) = V − E + F. This is cellular = singular homology for 2-complexes, via MV / excision on the face interiors.
4. Apply 3 twice: χ(E) = −6d for the cover's own complex; χ(Surface false 16) = 1 − 16 + 1 = −14 for its standard complex. Homeomorphism invariance identifies them.
5. `omega` on −14 = −6d.
Shared tags: covering-trivial-over-disk, polygon-cover-descent, polygon-complex-euler-characteristic (≈ polygon-surface-homology)
Doubts: The statement is true and faithfully encodes the problem; the superseded encoding was vacuous because it assumed χ multiplicativity. I found no lighter invariant. Rational H₁ plus transfer gives only b₁(E) ≥ b₁(B) (15 ≥ 7, no contradiction), and π₁ index arguments reduce to the same χ computation. Steps 1–2 are shared with t03J03 steps 5–6. Step 3 is the large part: tens of rows, with no existing homology computation for any polygon surface to start from.

### t91A07 — DIRECT — sorries: 1
Needs:
- `apm_t91a07`: in the chart `φ = extChartAt 𝓘(ℝ,E) x` at a fixed point, `g = φ ∘ f ∘ φ.symm` is C^∞ at `φ x` with `dg − id` bijective. The inverse function theorem makes `y ↦ g y − y` locally injective, so fixed points near `x` equal `x`.
Reuse: Mathlib `contMDiffAt_iff`, `ModelWithCorners.range_eq_univ`, `contDiffWithinAt_univ`, `ContDiffAt.hasStrictFDerivAt`, `HasStrictFDerivAt.sub`, `hasStrictFDerivAt_id`, `HasStrictFDerivAt.localInverse`, `.eventually_left_inverse`, `.localInverse_apply_image`, `extChartAt_source_mem_nhds`, `continuousAt_extChartAt`, `mem_extChartAt_source`, `PartialEquiv.left_inv`, `PartialEquiv.injOn`. It is the same argument as the in-file `apm_t91a07_previous_encoding`, transported through the chart.
Route:
1. Closure probe DONE: `/tmp/routes1/T91A07Probe.lean` states `probe_t91a07` with the exact frozen hypotheses and conclusion and proves it (~50 lines). It compiled with no errors or warnings (`lake env lean`, 2026-09-28). Paste it as the proof body of `apm_t91a07`.
Shared tags: none
Doubts: none. The statement uses the chart at x for both source and target, which is legitimate because f x = x. A C¹ hypothesis would have sufficed.

### t91J03 — FOUNDATION — sorries: 1
Needs:
- `apm_t91j03`: if γ : Circle → Circle × [0,1] is an embedding, and the H₁ map of `fst ∘ γ` acts as multiplication by n, then |n| ≠ 2. The route below proves |n| ≤ 1, which is stronger.
Reuse:
- In Main: `apm_t91J03_height_ne_of_circleMap_eq`, `apm_t91J03_no_two_of_forced_fiber_collision`. The latter is optional: the route below gives a contradiction directly and does not produce its "fibre collision" form.
- `CircleSingularHomology.circleSingularH1IsoInt`, `CircleHurewiczIsomorphism.circleAbelianizedFundamentalGroupH1MulEquiv`, `DegreeOneHurewiczMap.abelianizedFundamentalGroupToH1`, `CircleExponentialPathLift.lift` / `existsUnique_endpointWinding`, `CircleWindingUniqueness.endpointWinding_unique`, `PeriodicCircleHomotopyWinding` (square lifting via `IsCoveringMap.liftHomotopy`), `DegreeFourCircleWinding.degreeFour_not_homotopic_const` (template for "a loop that extends over the square has winding 0").
- No Jordan/Poincaré–Miranda/Brouwer in Mathlib or ConstructionTargets.
Route:
1. `circle-h1-degree`: for `c : C(Circle, Circle)` whose real lift over one turn has endpoint displacement `d·2π`, the H₁ map of `c` is `d •`. Needs naturality of `abelianizedFundamentalGroupToH1`, which is apparently not banked, plus `CircleHurewiczIsomorphism`. Consequence: `HasWindingNumber γ n → n = d`.
2. Periodic lift: a continuous `θ̃ : ℝ → ℝ` with `Circle.exp (θ̃ t) = (γ (exp 2πit)).1` and `θ̃ (t+1) = θ̃ t + 2πd` (path lift + uniqueness of lifts).
3. Disjointness (elementary): for |d| ≥ 2, the strip curves `L₀ = {(θ̃ t, h t)}` and `L₁ = L₀ + (2π, 0)` are disjoint. Equal points force γ(s) = γ(t), so s ≡ t mod 1, so θ̃ s − θ̃ t ∈ 2πdℤ, which cannot equal 2π.
4. `planar-crossing-lemma`: if β : [0,1] → ℝ×[0,1] runs from height 0 to height 1, and α : [0,1] → ℝ×[0,1] has `x(α 0) < min x∘β` and `x(α 1) > max x∘β`, then α and β meet. Proof: `(s,t) ↦ α s − β t` would be nonvanishing on the square. Its boundary loop visits {x<0}, {y≥0}, {x>0}, {y≤0} in cyclic order, so it has winding ±1, yet it extends over the square, so its winding is 0. This is the one substantial theorem (roughly 200–400 lines), and it is reusable for other planar separation problems.
5. Assembly: take L₁'s lowest point and highest point over one period (compactness). β = vertical segment from the bottom edge up to the lowest point, then the L₁ arc, then a vertical segment from the highest point to the top edge. β avoids L₀: L₀ has the same height range as L₁, and L₀ ∩ L₁ = ∅. α = L₀ restricted to a long parameter interval (θ̃ is unbounded both ways since d ≠ 0). Step 4 gives a contradiction, so |d| ≤ 1, so |n| ≠ 2.
Shared tags: planar-crossing-lemma, circle-h1-degree
Doubts: The statement is true as frozen. Route size: 5 steps, each one theorem. Only step 4 is substantial, and step 1 may need Hurewicz naturality proved first. It does not need the Jordan curve theorem: the min/max vertical-segment trick replaces the "below/above component" argument sketched in Main's comments.
### t91J05 — HEAVY — sorries: 3
Needs:
- `apm_t91J05_bridge_1`: every connected space X admitting a finite-fibred surjective covering map onto `Surface true 3` is homeomorphic to `Surface true (2n+1)` for some n > 0 (classification of the cover as a surface plus χ(X) = n·χ(Σ₃)).
- `apm_t91J05_bridge_2`: for n > 0, an explicit surjective covering map `Surface true (2n+1) → Surface true 3` with finite fibres.
- `apm_t91j05` (main): assembly only. Checked by compile (/tmp/routes1/F_assembly.lean): with the two bridges as hypotheses, the main theorem closes as `⟨apm_t91J05_bridge_1 X, fun ⟨n, hn, ⟨e⟩⟩ => apm_t91J05_isFiniteCover_of_homeomorph e (apm_t91J05_bridge_2 n hn)⟩`, so this sorry is DIRECT once the bridges exist.
Reuse: `ConstructionTargets.Surfaces` (`Surface`, `surfaceQuotient`, `continuous_surfaceQuotient`, `eulerCharacteristic`); the local `apm_t91J05_isFiniteCover_of_homeomorph` and `apm_t91J05_eulerCharacteristic_odd_genus`; Mathlib `IsCoveringMap`, `IsCoveringMap.comp_homeomorph`, `IsCoveringMap.existsUnique_continuousMap_lifts` (lifting over the simply connected open 2-cell). No surface classification, no covering-of-polygon-quotient construction, and no π₁ of `Surface true g` exists in ConstructionTargets or Mathlib.
Route:
1. `polygonQuotient_isCoveringMap_of_edge_pairing`: a quotient of k copies of a 4g-gon by an edge pairing that lies over the 12-gon pairing, with consistent vertex links, maps to `Surface true 3` by a covering map (local triviality at open-cell, edge-interior and vertex points). This is the lemma bridge_2 is built on.
2. `cyclicCover_polygon_model n`: the n-sheeted cyclic cover of Σ₃ (cut along one nonseparating edge class, glue n 12-gons cyclically) as an instance of step 1, with fibres of cardinality n.
3. `cyclicCover_polygon_model ≃ₜ Surface true (2n+1)`: a cut-and-paste homeomorphism between two polygon quotients (n glued 12-gons vs one 4(2n+1)-gon). This is the costly part of bridge_2 and needs an explicit polygon re-cutting argument.
4. `finiteCover_of_Surface_is_polygon_quotient`: for any finite cover X of `Surface true 3`, the open 2-cell is simply connected so its preimage is k disjoint open disks, and X is homeomorphic to a quotient of k 12-gons by an edge pairing (lifting + a quotient-map argument).
5. `classification_of_orientable_polygon_gluings`: a connected orientable edge-pairing quotient of polygons is homeomorphic to `Surface true g`, with g determined by V − E + F. This is the combinatorial classification of surfaces (normal-form reduction).
6. Orientability lifts to the cover, and χ multiplies: χ(X) = k·χ(Σ₃) = −4k, hence g = 2k+1 (uses `apm_t91J05_eulerCharacteristic_odd_genus`).
Size: steps 3 and 5 are each large programmes (each is tens of lemmas of polygon combinatorics and quotient topology); steps 1 and 4 are substantial single theorems. Realistically 60+ lemmas in total. No lighter route: the frozen statement quantifies over arbitrary connected X, so a classification theorem is unavoidable for bridge_1, and bridge_2 needs a homeomorphism onto the specific polygon model `Surface true (2n+1)`.
Shared tags: surface-classification, polygon-quotient-covering, covering-euler-characteristic, polygon-cut-and-paste-homeomorphism
Doubts: none about truth. `Surface true g` depends on `SurfaceRel` generating the right identifications at the polygon vertices (all 4g vertices to one point). This is standard for the word a b a⁻¹ b⁻¹, but no banked lemma checks it, and steps 1 and 4 need it. Shared with t00A02, which asks for genus-five covers of N₄ and has a similar classification sorry.

### t91J06 — ADAPTER — sorries: 3
(After repairing the bridge_glue helper signature, see Doubts. Four route steps plus a 2-line main assembly; steps 3 and 5 are each one theorem of moderate length.)
Needs:
- `apm_t91J06_bridge_compatible_stage_coordinates`: homeomorphisms g n from stage n to [-(n+1), n+1] such that g (n+1) restricts to g n on stage n.
- `apm_t91J06_bridge_glue_compatible_stage_coordinates`: compatible g, together with `hweak`/`hcover`, gives `X ≃ₜ ℝ`.
- `apm_t91j06` (main): assembly only. Checked by compile (/tmp/routes1/F_assembly.lean): `obtain ⟨g, hg⟩ := bridge_compatible … f hf hnested; exact bridge_glue … f hnested hcover hweak g hg` closes it.
Reuse: local `apm_t91J06_stage_compact`, `apm_t91J06_stage_mono`, `apm_t91J06_exists_mem_stage`, `apm_t91J06_exists_pair_mem_stage_interior`; Mathlib `Topology.IsEmbedding.toHomeomorph` (gives `I ≃ₜ range (f n)`, and `Set.image_univ` identifies the range with the stage), `ContinuousOn.strictMonoOn_of_injOn_Icc` / `Continuous.strictMono_of_inj_boundedOrder` (a continuous injection of an interval is monotone), `Continuous.homeoOfEquivCompactToT2`, `intermediate_value_Icc`, `ContinuousAt` via `Filter.EventuallyEq` on `Ioo (-(n+1)) (n+1)`. The names were confirmed with `#check`. Nothing relevant in ConstructionTargets.
Route:
1. `transition_interval`: for each n, `t n := (f (n+1))⁻¹ ∘ f n : I → I` is a continuous injection whose image is `Icc a b` with 0 < a < b < 1. It is monotone or antitone (strictMono lemma), and its image lies in the interior by `hnested`.
2. `extend_interval_homeomorph`: a strictly monotone continuous bijection `φ : Icc a b → Icc (-m) m` with 0 < a < b < 1 extends, by affine pieces on [0,a] and [b,1], to a strictly monotone continuous bijection `Φ : I → Icc (-(m+1)) (m+1)`. The antitone case is handled by composing with negation.
3. `compatible_coordinates_rec`: by `Nat.rec`, build `φ n : I → ℝ` (continuous, strictly monotone, image [-(n+1), n+1]) with `φ (n+1) ∘ t n = φ n`. Then set `g n := (IsEmbedding.toHomeomorph (hf n)).symm` followed by the homeomorphism from `φ n` (built with `homeoOfEquivCompactToT2`). Compatibility follows from `f (n+1) ∘ t n = f n`. This closes bridge_compatible; the main cost is bookkeeping with dependent subtypes.
4. `glue_equiv`: define `G x := g n ⟨x, _⟩` for any n with x in stage n. It is well defined by `hcompat` and `stage_mono` (induction on the difference of indices), injective via `exists_pair_mem_stage_interior` plus injectivity of g n, and surjective because ℝ = ⋃ [-(n+1), n+1].
5. `glue_homeomorph`: G is continuous because, for closed C ⊆ ℝ, the preimage `f n ⁻¹' (G ⁻¹' C) = (g n ∘ codRestrict (f n))⁻¹' C` is closed, and then `hweak` applies. G⁻¹ is continuous at y because on `Ioo (-(n+1)) (n+1)` with |y| < n+1 it agrees with `Subtype.val ∘ (g n).symm`.
Shared tags: none (self-contained one-dimensional argument; possibly `interval-homeomorph-extension` if another problem needs step 2)
Doubts: `apm_t91J06_bridge_glue_compatible_stage_coordinates` is FALSE as written, because it omits `hf`. Counterexample: let X be the image of an injective continuous curve γ : ℝ → ℝ² with γ(t) → γ(0) as t → +∞ (a figure-6), with the subspace topology, and let g n come from γ on [-(n+1), n+1]. Let each f n be a surjection of I onto stage n whose fibres are all dense (use the continuum many ℚ-cosets). Then `hnested` and `hcover` hold, and `hweak` holds vacuously: a set whose preimage under f n is closed must meet stage n in ∅ or in all of it. But X is not homeomorphic to ℝ: a homeomorphism would make t ↦ h(γ t) a strictly monotone map ℝ → ℝ that converges to its own value at 0. Fix: add `(hf : ∀ n, Topology.IsEmbedding (f n))` (continuity is enough) to this non-frozen helper; step 5 then goes through. The frozen `apm_t91j06` has `hf` and is true (the standard weak-union-of-arcs-is-ℝ argument). The main-assembly compile passes, but only because it forwards a false bridge. Do not elect a closure probe on the current bridge_glue.

### t92J05 — HEAVY — sorries: 3
(The RP² sorry is ADAPTER-sized, the main sorry is DIRECT, and the genus-two sorry is HEAVY. The problem closes only when the HEAVY part does.)
Needs:
- `apm_t92J05_bridge_projectivePlane_fundamentalGroup`: for every x, `FundamentalGroup (Projectivization ℝ (Fin 3 → ℝ)) x ≃* Multiplicative (ZMod 2)`, where the topology is the quotient topology from the nonzero vectors.
- `apm_t92J05_bridge_genusTwo_fundamentalGroup`: every T2, compact, path-connected smooth 2-manifold with the genus-two homology signature has π₁ ≃* ⟨a₁,b₁,a₂,b₂ | [a₁,b₁][a₂,b₂]⟩.
- `apm_t92j05` (main): assembly only. Checked by compile (/tmp/routes1/F_assembly.lean): `refine ⟨bridge_projectivePlane, fun x => ?_, bridge_genusTwo⟩; obtain ⟨hS2, hS1⟩ := apm_t92J05_bridge_sphere_circle_fundamentalGroups; haveI := hS2 x.1; exact apm_t92J05_product_group_of_subsingleton_left x.1 x.2 (hS1 x.2)`. The S²×S¹ conjunct is therefore already closed by existing sorry-free code.
Reuse: `ConstructionTargets.SimplyConnectedSphereProducts.euclideanSphere_simplyConnected 2` (S² simply connected); Mathlib `Topology.IsQuotientMap.isQuotientCoveringMap_of_properlyDiscontinuousSMul` (needs a quotient map, `ContinuousConstSMul`, `IsCancelSMul`, fibres = orbits, locally compact T2 source); `Finite.to_properlyDiscontinuousSMul` (instance; any finite group); `Topology.IsQuotientMap.of_comp`; `IsCoveringMap.monodromy`, `monodromy_map`, `injective_path_homotopic_map`, `liftPath`; `mulEquivOfPrimeCardEq` (any two groups of prime cardinality p are ≃*). The names were confirmed with `#check`. Also useful: `ConstructionTargets.ProjectiveSpaceTopology` (continuity/surjectivity pattern for the projection) and the t00A02 antipodal-cover lemmas (`apm_t00A02_antipodalCover_eq_iff`, `_fiber_card`), which are for a different RP² model and would need to be re-proved for `Projectivization`. For the genus-two clause: the van Kampen groupoid layer (`TwoOpenFundamentalGroupoidPseudopushout`, `TwoOpenFreeProductMapping`, `PointWedgeQuotient`, the `TwiceSpiralFundamentalGroup*` extraction pattern) covers the gluing step, but no surface classification exists.
Route (RP², ADAPTER, 5 steps):
1. `sphereToRP2 : S² → RP²`, `x ↦ Projectivization.mk ℝ x (ne_zero)`, is continuous and is a quotient map: normalisation `v ↦ v/‖v‖` on nonzero vectors is continuous and `sphereToRP2 ∘ normalise = mk`, so `IsQuotientMap.of_comp` applies.
2. A free `Multiplicative (ZMod 2)` (or `ℤˣ`) action on S² by x ↦ −x, with `ContinuousConstSMul` and `IsCancelSMul`; `sphereToRP2 x = sphereToRP2 y ↔ y = x ∨ y = −x`. Then `IsCoveringMap sphereToRP2` follows from `isQuotientCoveringMap_of_properlyDiscontinuousSMul(...).isCoveringMap`.
3. `fiber_card_two`: `Nat.card (sphereToRP2 ⁻¹' {x}) = 2` (x ≠ −x on the sphere).
4. `fundamentalGroup_equiv_fiber_of_simplyConnected_cover` (general, reusable): if p : E → X is a covering, E is simply connected and p e₀ = x, then `γ ↦ monodromy γ ⟨e₀, _⟩` is a bijection `FundamentalGroup X x ≃ p ⁻¹' {x}`. Injectivity: equal endpoints, lifts homotopic in E, and `Path.Homotopic.map` pushes the homotopy down. Surjectivity: project a path in E and apply `monodromy_map`. About 1 theorem, 40–80 lines.
5. `Nat.card (FundamentalGroup RP² x) = 2` by steps 3–4, then `mulEquivOfPrimeCardEq` with `Nat.card (Multiplicative (ZMod 2)) = 2`. Every x has a preimage, since `sphereToRP2` is surjective.
Route (genus two, HEAVY):
6. `smooth_compact_surface_classification`: a compact connected smooth 2-manifold is homeomorphic to some `ConstructionTargets.Surfaces.Surface o g` (needs a triangulation of smooth surfaces or Morse theory, then normal-form reduction). This is a large programme (100+ lemmas); the audit notes that rows 568–583 started on smooth-surface triangulation for t00A03/t99J03 without reaching it.
7. `surface_homology_determines_type`: compute H₁/H₂ of `Surface o g` (cellular or Mayer–Vietoris) and match the signature ℤ⁴, ℤ to (orientable, g = 2). This needs singular homology of the polygon quotients, which is also not banked.
8. `fundamentalGroup_polygon_surface`: π₁(`Surface true 2`) ≃* the one-relator group, via van Kampen for a 2-cell attached to a wedge of four circles (disk interior ∪ punctured-surface neighbourhood). The punctured polygon deformation-retracts onto the 1-skeleton, the wedge of four circles, with π₁ = F₄ (needs a wedge free-product theorem, shared with t92J06/t01A04). Attaching the cell kills the boundary word.
9. Transport π₁ along the homeomorphism (`BoundaryTorusHurewiczIsomorphism.fundamentalGroupMulEquivOfHomeomorph`) and the basepoint change (`FundamentalGroup.fundamentalGroupMulEquivOfPathConnected`).
Shared tags: antipodal-sphere-cover (with t00A02), simply-connected-cover-fiber-bijection, surface-classification, surface-singular-homology, seifert-van-kampen-cell-attachment, wedge-of-circles-free-group
Doubts: none about truth. H₂ = ℤ forces orientability and H₁ = ℤ⁴ forces genus 2, so the genus-two clause is true but only reachable through classification. There is no lighter route, because the frozen clause quantifies over arbitrary smooth surfaces. Recommend electing steps 1–5 now as a separate closure of the RP² bridge (step 4 is reusable, e.g. for t00A02/t97A03/t98A03 π₁ computations).

### t92J06 — HEAVY — sorries: 1
(Conjunct (b) is FOUNDATION + ADAPTER-sized. Conjunct (a), the universal cover, is HEAVY because of simple connectivity of an infinite graph.)
Needs (one sorry, the frozen conjunction):
- (a) a type E with a topology, a covering map p : E → wedge, and `SimplyConnectedSpace E` (the Cayley 4-regular tree).
- (b) four 3-sheeted `apm_t92J06_Covering 3` structures (every fibre has `Nat.card` = 3) whose total spaces are pairwise non-homeomorphic.
Reuse: local `apm_t92J06_wedgeDesc`/`_unique`/`_continuous_inl/inr`/`_inl_base_eq_inr_base` (maps out of the wedge); `ConstructionTargets.PointWedgeQuotient` (saturated open cover `leftOpen`/`rightOpen` of a point wedge, `quotientHomeomorphOfRelIff`); `ConstructionTargets.CircleUniversalCover.circleCover_isCoveringMap` (ℝ → Circle); `apm_t01A02_isCoveringMap_circle_pow_two`, Mathlib `AddCircle.isAddQuotientCoveringMap_nsmul` (z ↦ z^k covers); `ProductEvenlyCoveredTrivialization`; banked `apm_t00J06_isCoveringMap_fst_nat` (trivial covers S × ℕ; adapt to `Fin 3`); Mathlib `IsCoveringMap`, `IsEvenlyCovered`, `ConnectedComponents`, `Homeomorph` transport of connectedness. No graph-realisation, wedge-cover gluing, or tree simple-connectivity result exists. t01A04's descended cover maps (`apm_t01a04_circleCoverMap` etc.) are built the same way but their covering property is still a sorry there.
Route:
1. `wedge_cover_of_circle_covers` (FOUNDATION, reusable): given coverings q₁ : E₁ → S¹ and q₂ : E₂ → S¹ and a bijection φ : q₁⁻¹{1} ≃ q₂⁻¹{1}, the glued space (E₁ ⊕ E₂)/(e ∼ φ e) maps to the wedge by a covering map with fibres ≅ q₁'s fibres. Local triviality away from the base uses the two open pieces; at the wedge point, take the union of evenly-covered arcs of both circles through each fibre point. For arbitrary (possibly infinite) index types.
2. `permutation_cover σ τ` (for σ τ : Equiv.Perm (Fin 3)): take E₁ = the cover of S¹ with monodromy σ (a disjoint union over cycles of z ↦ z^len), similarly E₂ for τ, and glue by step 1. This gives `apm_t92J06_Covering 3`, with `fiberCard` from the fibre bijection.
3. Choose four covers: (i) trivial, `wedge × Fin 3` (3 components); (ii) `wedge ⊕ D` with D the connected double cover of σ = τ = swap (2 components; needs a small `IsCoveringMap` for `Sum.elim`); (iii) connected C₁ with σ = (123), τ = id (3 b-loops); (iv) connected C₂ with σ = τ = (123) (no loops).
4. `nonhomeomorphic_by_components`: the number of connected components (1, 2, 3) is a homeomorphism invariant (`ConnectedComponents` + `Homeomorph`), which separates (i), (ii) and {(iii), (iv)}. Needs a connectedness proof for (iii) and (iv) and a component count for (i) and (ii).
5. `C₁_has_cut_point` / `C₂_no_cut_point`: removing the vertex of a b-loop in C₁ disconnects it (the open loop arc is clopen in the complement). Removing any single point of C₂ leaves it connected (case split: vertex or edge interior; each vertex joins the other two by ≥ 2 edges). "Has a cut point" is homeomorphism-invariant, which gives C₁ ≄ C₂. This closes (b).
6. `cayleyTree_cover` (conjunct (a), covering part): apply step 1 with E₁ = (FreeGroup (Fin 2) ⧸ ⟨a⟩-cosets) × ℝ over `circleCover`, E₂ likewise for b, and φ identifying both fibres with FreeGroup (Fin 2).
7. `cayleyTree_simplyConnected` (HEAVY): the glued tree is path-connected (induction on reduced words) and has trivial π₁. The route is either a contraction to the identity vertex (a homotopy defined edge-wise with depth-dependent speed; continuity on I × E through `IsQuotientMap.continuous_lift_prod_left`, since I is locally compact), or: every loop is compact, so it lies in a finite subtree; finite trees contract by induction on leaves. Either way this is roughly 15–30 lemmas of quotient-topology and word-combinatorics work. The alternative through the π₁ action (π₁(wedge) ≅ F₂ by van Kampen, free transitive monodromy on the fibre) is not lighter; it needs the same van Kampen wedge computation that t92J05 step 8 needs.
Shared tags: wedge-quotient-covering-gluing (with t01A04, t98A03, t97A03), graph-cut-point-invariant, infinite-tree-simply-connected, wedge-of-circles-free-group (only on the alternative route to (a))
Doubts: none about truth; the frozen statement is standard. Part (b) is bounded (steps 1–5, of which step 1 is the reusable piece). Part (a) is the expensive half. Recommend electing step 1 first, since it also unblocks t01A04's `apm_t01A04_bridge_quotient_maps_are_coverings`.

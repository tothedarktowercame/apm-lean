# Fidelity grades — open list 2

Grader: read-only; nothing in /home/joe/code/apm-lean was built, run or edited. No bundle in this list has a STATEMENT-REPAIR.md (checked with find). Statements read at HEAD 56de913a. Note: in every bundle the registered theorem is named with a lowercased id (e.g. `apm_t00a03`, `apm_tunk01`); there is no declaration spelled exactly `apm_<id>` with the capital A/J.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00A03 | faithful | `apm_t00a03` (lowercase a; no `apm_t00A03`) | Real compact smooth surface with genus pinned by singular homology; maximal family of embedded, non-null-homotopic, pairwise disjoint, pairwise non-freely-homotopic circles; every complementary component ≃ₜ open pants model, and n = 3g-3 | YES: printed "3g-g" is false (g=2 gives 4, true max is 3); corrected to 3g-3 |
| t00J07 | faithful | `apm_t00j07` (lowercase j) | Actual quotient RP² ⊔ D² / (f z ~ ∂z); (a) null-homotopic f gives π₁ ≅ ℤ/2, H = (ℤ, ℤ/2, ℤ, 0…); (b) essential f gives π₁ trivial, H = (ℤ, 0, ℤ, 0…) | no |
| t01A02 | faithful | `apm_t01a02` (lowercase a) | (a) the actual singular H₂ morphism of a nonsurjective f is 0; (b) the concrete (z,w) ↦ (z²,w²) is a covering with a free fibre-transitive (ℤ/2)² deck action; (c) f = cover ∘ g ⇒ fixed point | no |
| t01A08 | stronger | `apm_t01a08` | Answers "yes" and asserts more than a smooth preimage: some vertical line ℓ_p = π⁻¹(p) with p a regular value of π∘f, i.e. f is transverse to ℓ_p. True by Sard (X second countable) | minor: codomain written once as "A", once as 𝐀³; read as ℝ³. No narrowing results |
| t01J05 | false | `apm_t01j05` (lowercase j) | X is not assumed Hausdorff. The circle with a doubled point is a compact boundaryless smooth 1-manifold in Mathlib's sense, with a nowhere-zero 1-form, and it has χ = 1 − 2 = −1 | no |
| t02A05 | faithful | `apm_t02a05` | Outward flux over the unit sphere centred at c, as an integral against μH[2] on the sphere; minimum 44π/15, attained exactly when c₀ = 1, c₁ = 2 | minor: "the sphere" suggests a unique minimiser, but every centre (1,2,t) minimises. The statement characterises the whole family, which is correct |
| t03J01 | hypothesis-carries-core | `apm_t03j01` (lowercase j) | Part (b) follows from hypothesis `hcut₂`, which includes "J₂ is null-homologous" (`H1Map (inclusion J₂) = 0`). Given that, no retraction needs only H₁(S¹) ≠ 0, and the file already derives it that way. For (a), `hcut₁` supplies a homomorphism H₁(X) → ℤ sending [J₁] to 1 | YES: a curve cannot cut a genus-2 surface into a twice-punctured sphere (χ −2 vs 0); corrected to twice-punctured torus (nonseparating curve) |
| t03J04 | narrower (accepted under PRELIM-DEFECT) | `apm_t03j04` (lowercase j) | Adds n ≥ 1, X connected and X Hausdorff, and drops orientation-preservation. Conclusions: the constant field is nowhere zero, χ(Tⁿ) = 0, and χ(X) = 0 for every local diffeomorphism Tⁿ → X | YES: without "X connected" χ(X) is unconstrained (extra components), and for n = 0 the answer is 1 |
| t91J05 | faithful | `apm_t91j05` (lowercase j) | A connected space X is a finite cover of the concrete genus-3 polygon surface iff X ≃ₜ Σ_{2n+1} for some n ≥ 1 | minor: "which spaces" does not say connected; the connected reading is conventional, and the header explains why disconnected covers are left out |
| t92J06 | faithful | `apm_t92j06` (lowercase j) | (a) there is a simply connected covering space of the actual wedge quotient S¹ ∨ S¹; (b) there are four 3-sheeted coverings (exact 3-point fibres) with pairwise non-homeomorphic total spaces | minor: "sketch" requests have no formal counterpart; encoded as existence |
| t93A06 | faithful | `apm_t93a06` (lowercase a) | For some smooth atlas on (ℝ/ℤ)² that makes the quotient a local diffeomorphism: ω′ exists and is the unique smooth form with π*ω′ = ω, ∫ω′ = 1/4, and ω′ is not exact; the explicit η has dη = ω; the parallelogram integral of η is 1/4 | no |
| t93J04 | faithful | `apm_t93j04` (lowercase j) | The two inclusions S² → S²×S² (x ↦ (x,p) and x ↦ (p,x)) are not (continuously) homotopic. This answers "no" and implies they are not smoothly homotopic | no |
| t94A03 | faithful | `apm_t94a03` (lowercase a) | No sequence of subsets of ℝ, each homeomorphic to Cantor space ℕ → Bool, covers ℝ | no |
| t94A07 | faithful | `apm_t94a07` (lowercase a) | For the standard torus of revolution (z-axis, 0 < r < R) and (x,y,z) ↦ (x,−y,−z): exactly the 4 points (±R±r,0,0) are fixed, all are Lefschetz (no fixed nonzero tangent vector), det(I−Df) = 4 and the local index is +1, and there is no homotopy to id through the torus | no |
| t94A10 | faithful | `apm_t94a10` (lowercase a) | For any ω on ℝ³∖0 given pointwise by the printed formula: ω is differentiable with extDeriv 0 there, and there is no η on ℝ³∖0 that is differentiable with extDeriv η = ω | no |
| t94J09 | faithful | `apm_t94j09` (lowercase j) | The actual quotient of the 14-gon under the seven printed pairings is homeomorphic to the standard N₆ polygon quotient, with H₀ = ℤ, H₁ = ℤ⁵ ⊕ ℤ/2, H_{≥2} = 0; also V = 2, E = 7, χ = −4 and nonorientable | problem.md's embedded \soln sketch gives N₃, which is wrong (flagged "not to be trusted" in the source). The problem text and its vertex note are consistent, so no departure results |
| t95A04 | faithful | `apm_t95a04` (lowercase a) | For some smooth atlas on the quotient RP² that makes S² → RP² a local diffeomorphism, the map f̃ determined on sphere representatives by the six printed coordinates is smooth, a topological embedding, and an immersion | no |
| t95J06 | faithful | `apm_t95j06` (lowercase j) | (a) the torus T is invariant under H(z,t) = e^{it}z; (b) every compact surface in S⁵ that is invariant under H, carries some 2-dim atlas, and has H₂ ≅ ℤ on each component, has every component ≃ₜ S¹×S¹ | no |
| t96A04 | faithful | `apm_t96a04` (lowercase a) | `¬ IsCompact (univ : Set C(I, I))` for I = [0,1] | no |
| t96A07 | faithful | `apm_t96a07` (lowercase a) | For some atlas on RP² making S² → RP² a local diffeomorphism: (a) f̄ exists with f̄∘π = f and is smooth; (b) f̄ is not transverse to the z-axis; (c) infinitely many z₀ have the plane z = z₀ transverse to f and meeting im f | no |
| t96J02 | faithful | `apm_t96j02` (lowercase j) | Every finite-index subgroup of π₁(K), with K the actual aabb polygon quotient, is ≅ π₁(K) or ≅ ℤ², and both occur | no |
| t97A01 | faithful | `apm_t97a01` (lowercase a) | For the aabbcc hexagon quotient (N₃) and the aba⁻¹b⁻¹cc quotient (T²#RP²): H₀ = ℤ, H₁ = ℤ² ⊕ ℤ/2, H_{≥2} = 0; and π₁(T²#RP²) ≅ ⟨a,b,c ∣ aba⁻¹b⁻¹c²⟩ | no |
| t97A05 | faithful | `apm_t97a05` (lowercase a) | For smooth embeddings Yⁿ⁺¹ → Xⁿ⁺ᵏ, Wⁿ → Y, Zᵏ → X (all boundaryless and Hausdorff, Y, W, Z compact, Y and W connected, orientations given as volume forms): if the signed count of W ∩ Z′ is value ≠ 0 for some smooth transverse Z′ homotopic to Z, then Y ∖ W is connected | no |
| t97J02 | faithful | `apm_t97j02` (lowercase j) | Over the concrete N₄ polygon quotient: N₁₂ 5-fold covers it, and every compact connected surface 5-fold covering it is ≃ₜ N₁₂; Σ₇ and N₁₄ 6-fold cover it, and every 6-fold cover is ≃ₜ Σ₇ or N₁₄ | no |
| t97J07 | narrower | `apm_t97j07` (lowercase j) | (a) is stated properly: fixed set = {z₂ = 0} ∪ {[0:0:1]}. But (c), χ(CP²), becomes `LineContribution + IndexFromDet PointDet = 3`, which is arithmetic on file-defined numbers and never mentions any Euler characteristic of CP². The line's contribution also hard-codes χ(CP¹) = 2 | YES (partial): diag(1,1,3) fixes a whole CP¹, so "the local Lefschetz number of each fixed point" is undefined on the line. This justifies a fixed-component contribution for (b), but it does not force dropping (c) |
| t98A03 | faithful | `apm_t98a03` (lowercase a) | For the actual wedge quotient T² ∨ RP²: it is not a topological manifold of any dimension; π₁ ≅ ℤ² ∗ ℤ/2; it has a connected regular 3-fold cover; and it has a connected irregular 3-fold cover | minor: part (d) lacks a question mark |
| t98J01 | faithful | `apm_t98j01` (lowercase j) | The alternating trace of h on rational singular homology of S²×S¹×S¹ is 8 (with finite-dimensionality and vanishing certificates), and h is not homotopic to id | no |
| t99A01 | narrower | `apm_t99a01` (lowercase a) | No space appears. It states only group-presentation facts (⟨x∣x²⟩ ≅ ℤ/2, ⟨x∣x²,x⁴⟩ ≅ ℤ/2, ⟨x∣x²,x⁴,x⁵⟩ = 1) and kernels of hand-written cellular boundary maps (0, ℤ, ℤ²). H₀ and H₁ are dropped, and so is the van Kampen / cellular comparison to the actual spaces | no |
| t99A04 | vacuous | `apm_t99a04` | The surface, embedding, closed forms and separation hypothesis are all gone. What remains is the fundamental theorem of calculus for a loop on [0,1] (∫ g′ = g(1) − g(0) = 0) and ∫₀¹ c = c | YES: "F" is undefined, and (a) needs X closed. On a compact annulus the core circle separates, yet dθ has period 2π. This does not force dropping the topology |
| t99J04 | faithful | `apm_t99j04` (lowercase j) | (a) answers "yes": n smooth functions whose differentials at x are linearly independent give a coordinate map that is a local diffeomorphism at x. (b) A smooth map from a nonempty compact Hausdorff manifold to a connected Hausdorff manifold, with bijective mfderiv everywhere, is surjective | minor: (b) needs X nonempty (empty X is a counterexample), and "in" is read as "is" in (a). Both are handled explicitly |
| tunk01 | faithful | `apm_tunk01` | Same problem as t94J09. Any X homeomorphic to the actual 14-gon quotient is homeomorphic to the standard N₆ quotient; plus V = 2, E = 7, χ = −4 and nonorientable | no. The problem text and its vertex note are consistent; see t94J09 for the vertex-class computation |

## Evidence notes

### t00A03

Evidence: conclusion `(∀ x ∈ apm_t00a03_cut curves, Nonempty (connectedComponentIn (apm_t00a03_cut curves) x ≃ₜ apm_t00a03_Pants)) ∧ n = 3 * g - 3`. Genus: `apm_t00a03_hasGenus` gives H0 ≅ ℤ, H1 ≅ ℤ^{2g}, H2 ≅ ℤ, H_k = 0 for k ≥ 3 (orientable closed genus g). Maximality `hmax : ∀ c, IsEmbedding c → ¬nullHomotopic c → (∀ i, disjoint c (curves i)) → ∃ i, parallel c (curves i)` is exactly "no curve can be added". Encoding choices: "bounds a disk" read as null-homotopic, "co-bound an annulus" read as free homotopy up to a self-homeomorphism of the circle (equivalent for disjoint essential simple curves on a surface); `ChartedSpace`/`IsManifold ⊤` restricts F to smooth surfaces (every surface admits one). `apm_t00a03_Pants` = open disk radius 3 minus two closed disks radius 1/2, which is homeomorphic to S² minus 3 points, the interior of a pair of pants. The two `apm_t00A03_bridge_*` theorems are `sorry` proof steps, not statement placeholders; no def in the statement is opaque/axiom/sorry.

### t00J07

Evidence: conclusion `(∃ p, Homotopic f (const _ p)) → apm_t00j07_invariants f (Multiplicative (ZMod 2)) (ModuleCat.of ℤ (ZMod 2))` and the negation → `invariants f (Multiplicative (ZMod 1)) (ModuleCat.of ℤ (ZMod 1))`. `invariants` = FundamentalGroup at the disk-centre basepoint, and integral singular H0 ≅ ℤ, H1 ≅ given, H2 ≅ ℤ, H_k zero for k ≥ 3. Checked the answers: (a) the curve bounds a disk, so X ≃ RP² ∨ S²: π₁ = ℤ/2, H₁ = ℤ/2, H₂ = ℤ. (b) an essential simple curve is isotopic to RP¹, X ≃ RP²/RP¹ ≅ S² (cellular: 2-cells with boundary degrees 2 and 1, H₂ = ker(ℤ² → ℤ) = ℤ). Topology on RP² is the quotient topology on `Projectivization`; the adjunction space is coinduced from the sum. The "find" part is answered by the fixed values in the statement. Bridge theorems are sorry proof steps only.

### t01A02

Evidence: `apm_t01A02_H2map f = 0 ∧ apm_t01A02_hasCoveringGroup (G := ZMod 2 × ZMod 2) apm_t01A02_cover ∧ ((∃ g, ∀ x, f x = apm_t01A02_cover (g x)) → ∃ x, f x = x)`. (b) is stated for one explicit covering, which proves the existence claim. In (c) the second factor is the covering map from (b), which is the only reading under which "factors through S" is non-trivial. (c) is true: deg f = 0 and f_* = p_* g_* = 2g_* on H₁, so the Lefschetz number 1 − tr + 0 is odd, hence nonzero. `hasCoveringGroup` requires IsCoveringMap, a continuous action by the group, freeness and `p x = p y ↔ ∃ g, act g x = y`; this pins the covering group.

### t01A08

Evidence: `∃ p, ∀ x, f x ∈ apm_t01a08_line p → Function.Surjective (mfderiv I apm_t01a08_I2 (fun z => apm_t01a08_projection (f z)) x)`. Transversality implies f⁻¹(ℓ_p) is an embedded submanifold, but not conversely, so the header's claim that the criterion is "equivalent" is wrong; this makes the statement stronger, not unfaithful. Only lines parallel to the x₃-axis are offered, which is still enough by Sard (critical values of π∘f have measure zero in ℝ²). General model with corners `I` allows boundary. Sard still gives measure-zero critical values, so the statement remains true. Second countability is assumed, and the header explains why it is needed.

### t01J05

Evidence: hypotheses are `[TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold … ⊤ X] [BoundarylessManifold …] [CompactSpace X]`, with no `T2Space X`. Counterexample, n = 1: X = S¹ with one point doubled. The two charts are the two copies of S¹ (each missing the other copy of the point), with smooth angle transitions. Pulling dθ back along the local diffeomorphism X → S¹ gives a nowhere-zero smooth section. Mayer–Vietoris for the open cover U = X∖{o₂} ≅ S¹, V = X∖{o₁} ≅ S¹, U∩V ≅ ℝ gives H₀ = ℚ, H₁ = ℚ², so `apm_t01J05_eulerCharacteristic 1 X = 1 − 2 = −1 ≠ 0`. Second defect: `apm_t01J05_IsOrientation X := Nonempty (∀ x, Orientation ℝ (TangentSpace … x) (Fin n))` asks for a pointwise orientation with no continuity, so it always holds and the orientability hypothesis is vacuous. With `[T2Space X]` added, the statement would be true and stronger (χ = 0 also holds for non-orientable X). Part (a) is a request for a definition: `apm_t01J05_IsPartitionOfUnitySubordinate` is provided but does not appear in the theorem.

### t02A05

Evidence: `(∀ c, 44π/15 ≤ apm_t02a05_outwardSphereIntegral omega c) ∧ (∀ c, … = 44π/15 ↔ c 0 = 1 ∧ c 1 = 2)`. I checked the value by divergence: div F = 3(x−1)² + 3(y−2)² + 1. Over the unit ball at c = (a,b,e) this integrates to 3(4π/15 + (4π/3)(a−1)²) + 3(4π/15 + (4π/3)(b−2)²) + 4π/3 = 44π/15 + 4π((a−1)² + (b−2)²). `isOmega` is ω_x(v,w) = F(x)·(v×w). `orientedCoefficient` = n₀ω(Pe₁,Pe₂) − n₁ω(Pe₀,Pe₂) + n₂ω(Pe₀,Pe₁). Since Pv×Pw = ((v×w)·n)n for the projection onto n^⊥, this equals (F·n)|n|² = F·n with the outward radial n. So it is the correct outward flux density. There is no opaque data; ω is given by a pointwise defining hypothesis, and such an ω exists.

### t03J01

Evidence: `apm_t03j01_CutsIntoTwoOncePuncturedTori J := ¬IsConnected (Jᶜ) ∧ apm_t03j01_IsNullHomologous J` and `apm_t03j01_CutsIntoTwicePuncturedTorus J := IsConnected (Jᶜ) ∧ apm_t03j01_HasPrimitiveClass J`. The file's own `apm_t03j01_no_retraction_of_curve_H1Map_zero` closes (b) from `hzero` (the hypothesis) plus `∃ a : H1 Circle, a ≠ 0`. That J₂ is null-homologous, because it bounds a once-punctured torus, is the step (b) asks for. Both homological conjuncts are true consequences of separating / nonseparating for a simple closed curve, so the statement is true. But a faithful encoding would state only the topological cutting condition (connectedness of Jᶜ) and derive them. Surface setup is sound: compact T2 path-connected smooth 2-manifold with H = (ℤ, ℤ⁴, ℤ, 0…) is the closed orientable genus-2 surface. `RetractsOnto J := ∃ r : C(X, J), ∀ y : J, r y = y` is a real retraction.

### t03J04

Evidence: the three conjuncts are `∀ q, apm_t03J04_constantVectorField n q ≠ 0`, `eulerCharacteristic n (Torus n) = 0`, and `∀ X [T2Space X] … [ConnectedSpace X] phi, IsLocalDiffeomorph … phi → eulerCharacteristic n X = 0`. The added hypotheses are forced or conventional. Connectedness: X = φ(Tⁿ) ⊔ Y lets χ(X) take any value, so the source's intended answer {0} needs it. Hausdorffness: Mathlib manifolds omit it, and the header's doubled-circle counterexample is right. Dropping orientation makes (b) stronger and still true: φ is a finite covering onto X, and χ(Tⁿ) = d·χ(X). The value 0 is attained by X = Tⁿ via conjunct 2, so "list all possible values" is fully answered. Two notes. (i) Part (a)(i) as encoded is trivial: `constantVectorField` is a constant nonzero function into `Fin n → ℝ¹`, not tied to the tangent bundle. The intended example (a constant field) is trivial anyway. (ii) `[ChartedSpace …] [IsManifold …]` on `Torus n` are theorem binders, so the statement quantifies over every smooth structure on the product-topology torus. This is harmless: χ is topological and the covering argument does not use the smooth structure.

### t91J05

Evidence: `[ConnectedSpace X] : apm_t91J05_IsFiniteCover X ↔ ∃ n, 0 < n ∧ Nonempty (X ≃ₜ Surface true (2*n+1))`. `IsFiniteCover` = `IsCoveringMap p ∧ Surjective p ∧ ∀ s, (p ⁻¹' {s}).Finite`. `ConstructionTargets.Surfaces.Surface true g` is a real quotient: the closed unit disk with its boundary cut into 4g arcs, glued by the word a₁b₁a₁⁻¹b₁⁻¹… (arc 4j at parameter t glued to arc 4j+2 at 1−t, and likewise 4j+1 with 4j+3). It is not opaque. The answer is correct: an n-sheeted cover has χ = −4n = 2 − 2g′, so g′ = 2n+1, and every such cover exists. Disconnected finite covers (finite disjoint unions) are excluded. That is the only departure, and it is the standard reading.

### t92J06

Evidence: `(∃ E _ p, IsCoveringMap p ∧ SimplyConnectedSpace E) ∧ ∃ C : Fin 4 → apm_t92J06_Covering 3, Pairwise fun i j ↦ ¬Nonempty (C i).E ≃ₜ (C j).E`. `apm_t92J06_Covering 3` requires `IsCoveringMap` and `Nat.card` of every fibre = 3, so fibres are finite of size 3. X is the real quotient of two circles with basepoints identified. The "sketch" is reduced to existence. Any proof must build the covers (the 4-regular tree, and four 3-fold graphs), but the statement does not pin which ones. This is a reasonable encoding of a sketch question. Coverings need not be connected; the problem does not ask for connected ones, and four non-homeomorphic 3-fold covers exist either way.

### t93A06

Evidence: `∃ atlas : SmoothAtlas, … (∃ form, IsSmooth form ∧ pullback projection form = sourceForm ∧ (∀ other, IsSmooth other → pullback projection other = sourceForm → other = form) ∧ torusIntegral form = 1/4 ∧ ¬IsExact form) ∧ IsSmooth primitive ∧ exteriorDerivative primitive = sourceForm ∧ parallelogramIntegral primitive = 1/4`. Definitions in ConstructionTargets/TorusFormTargets.lean and ManifoldFormTargets.lean are concrete: no opaque, axiom or sorry. The `SmoothAtlas` fields force the projection to be a local diffeomorphism, which fixes the standard smooth structure, so the ∃ is harmless. Checked values. `primitive` = (x/2 − sin(4πx)/(8π))cos²(2πy) dy has d = sin²(2πx)cos²(2πy) dx∧dy (areaForm = det, matching extDeriv's convention). ∫_{[0,1]²} = (1/2)(1/2) = 1/4. The parallelogram (0,0),(1,0),(2,1),(1,1) is traversed counter-clockwise and is a lattice fundamental domain of area 1, so ∫_γ η = 1/4. `parallelogramIntegral` sums the four printed edges in order. Minor: uniqueness is quantified over smooth forms only; uniqueness among all forms is also true and immediate, so nothing of substance is lost.

### t93J04

Evidence: `¬ (apm_t93j04_left p).Homotopic (apm_t93j04_right p)`, with left = `prodMk id (const p)` and right = `prodMk (const p) id` on the literal unit sphere in ℝ³. Continuous non-homotopy is at least as strong as smooth non-homotopy (and equivalent to it, by Whitney approximation). The answer is correct: their H₂ classes are (1,0) and (0,1).

### t94A03

Evidence: `¬ ∃ C : ℕ → Set ℝ, (∀ n, Nonempty ((ℕ → Bool) ≃ₜ C n)) ∧ ⋃ n, C n = univ`. "Cantor set" read topologically as a homeomorph of the Cantor space. A ℕ-indexed family also covers finite families (repeat an entry). The claim is true by Baire, since each such set is compact and totally disconnected, hence closed and nowhere dense in ℝ.

### t94A07

Evidence: conjuncts are the fixed set = `apm_t94a07_fixedPoints R r`; for each such p, `IsLefschetzFixedPoint`, tangent = span{e_y,e_z}, Df e_i = −e_i, `det (localMatrix p) = 4` and `localLefschetzNumber p = 1`; `Nat.card … = 4`; and `¬IsHomotopyToIdentity R r`. Answers check: Df = −I on T_p, so det(I−Df) = 4. The sum of indices is 4 ≠ χ(T²) = 0, so the map is not homotopic to id. `IsHomotopyToIdentity` asks for H : ℝ → ℝ³ → ℝ³ that is jointly continuous on all of ℝ×ℝ³ and keeps the torus in itself for t ∈ [0,1]. Any homotopy [0,1]×T → T extends to such an H by Tietze (the target ℝ³ is convex and [0,1]×T is closed), so the negation is equivalent to "no homotopy". "A smooth torus centred on the origin" is read as the torus of revolution about the z-axis. This is the reading under which the half-turn about the x-axis is a self-map.

### t94A10

Evidence: `apm_t94a10_IsClosed omega ∧ ¬apm_t94a10_IsExact omega`. `IsOmega` checked: x(v₀₁v₁₂ − v₀₂v₁₁) − y(v₀₀v₁₂ − v₀₂v₁₀) + z(v₀₀v₁₁ − v₀₁v₁₀), divided by r³, is (x dy∧dz − y dx∧dz + z dx∧dy)/r³. Extending by 0 at the origin and using `extDeriv` only at nonzero points is sound, since extDeriv at x ≠ 0 depends only on a neighbourhood. Non-exactness quantifies over merely differentiable η, not smooth η. That makes the claim somewhat stronger, and it is still true: Stokes/Green holds for differentiable forms with continuous exterior derivative, and ∫_{S²} ω = 4π ≠ 0. There is no placeholder; ω is fixed by a pointwise defining hypothesis that has a model.

### t94J09

Evidence: I recomputed the vertex classes from the signed word with v_i = start of edge i. The pairings give v0=v12, v1=v13 (a); v6=v13, v7=v0 (b); v1=v8, v2=v7 (c); v3=v9, v2=v8 (d); v6=v11, v5=v10 (e); v4=v11, v5=v12 (f); v4=v10, v3=v9 (g). That leaves two classes: {3,9} and the rest. So the problem's note (the corner between d⁻¹ and g⁻¹ is special) is correct, and V = 2, E = 7, F = 1, χ = −4. `a` occurs twice with the same sign, so the surface is nonorientable, N₆. I checked `apm_t94J09_PolygonRel` against the word: same-sign pairs glue t↔t and the opposite-sign pair c glues t↔1−t, as required. The key conjunct is `Nonempty (apm_t94J09_PolygonSurface ≃ₜ apm_t94J09_N6)`, and it depends only on the pairings. The hand-written `vertexClass` feeds only the arithmetic conjuncts, and it agrees with the computed classes. The header calls the switch from N₃ to N₆ a "repair", but it follows the problem statement and departs only from the untrusted solution sketch.

### t95A04

Evidence: `∃ atlas : SmoothAtlas 2, … ∃ f, (∀ p, f (sphereProjection 2 p) = T95A04SphereMap p) ∧ ContMDiff (𝓡 2) (𝓡 6) ∞ f ∧ Topology.IsEmbedding f ∧ Manifold.IsImmersion (𝓡 2) (𝓡 6) ∞ f`. `SmoothAtlas` (ConstructionTargets/RealProjectiveSmoothTarget.lean) requires the atlas to make `sphereProjection` a local diffeomorphism, which fixes the standard structure; the ∃ is harmless. `sphereProjection` is surjective, so f is uniquely pinned. A smooth immersion that is a topological embedding is a smooth embedding onto an embedded submanifold, as the problem asks. The topology on `Space ℝ 2` is the quotient topology. There are no opaque or axiom declarations.

### t95J06

Evidence: `IsInvariant H T ∧ ∀ F, IsCompactOrientableSurface F → IsInvariant H F → EveryComponentDiffeomorphicToTorus F`. `isHopfFlow` fixes H by the formula `exp(I t) • z`, which is the flow of v(z) = iz. The atlas in `IsCompactOrientableSurface` is existential and need not be compatible with S⁵'s smooth structure, so F ranges over topological surfaces that admit some smooth atlas. That widens the hypothesis. The claim remains true: z ↦ e^{it}z is free on S⁵, so F is a principal S¹-bundle over a closed 1-manifold, hence a torus or Klein bottle per component, and H₂ ≅ ℤ excludes the Klein bottle. "Diffeomorphism type" is encoded as homeomorphism per component, which is equivalent for surfaces. Disconnected F (disjoint unions of tori) is covered by the per-component form. The (a) proof is already complete in the file.

### t96A04

Evidence: `theorem apm_t96a04 : ¬ IsCompact (Set.univ : Set C)` with `C = ContinuousMap I I`. Mathlib's topology on `C(I,I)` is compact-open, which equals the sup-metric topology because I is compact. The answer ("disprove") is correct: take f_n(x) = xⁿ, or use Arzelà–Ascoli's failure of equicontinuity.

### t96A07

Evidence: conjuncts `(∀ p, f (sphereProjection 2 p) = sphereMap p) ∧ ContMDiff … f ∧ ¬Transverse f axis ∧ {z | Transverse sphereMap (plane z) ∧ ∃ p, sphereMap p 2 = z}.Infinite`. `Transverse` is range(mfderiv f) ⊔ range(fderiv g) = ⊤ at every incidence, which is the standard definition. Answers check. (b): along the equator f = (0,0,xy), and d(yz), d(xz) are both multiples of dz there, so the transverse component has rank ≤ 1 and the map is not transverse. (c): the critical values of xy on S² are 0 and ±1/2, so every z₀ ∈ (−1/2,1/2)∖{0} works. Part (c) uses the sphere map, "f" as printed; the header records this choice. The atlas ∃ is pinned by the local-diffeomorphism field.

### t96J02

Evidence: `(∀ H, H.FiniteIndex → Nonempty (H ≃* G) ∨ Nonempty (H ≃* Multiplicative (ℤ × ℤ))) ∧ (∃ H, FiniteIndex ∧ ≃* G) ∧ (∃ H, FiniteIndex ∧ ≃* ℤ²)`. G = `FundamentalGroup KleinBottle (surfacePoint false 2)`, with `KleinBottle := Surface false 2`, the disk quotient glued by the word aabb in ConstructionTargets/Surfaces.lean. It is concrete. The answer is correct: finite covers of K are Klein bottles or tori.

### t97A01

Evidence: seven conjuncts over `apm_t97a01_X` and `apm_t97a01_TorusRP2`, both concrete disk quotients. `RelX` is shown equal to `Surfaces.SurfaceRel false 3`. `RelTorusRP2` glues edge 0 to edge 2 reversed (a…a⁻¹), 1 to 3 reversed, and 4 to 5 same-direction (cc), matching the word. Values check: both surfaces are N₃ (χ = −1), so H₁ = ℤ²⊕ℤ/2 and H₂ = 0, and the one-relator presentation is correct. Method prescriptions ("using the CW decomposition", "Mayer–Vietoris", "Van Kampen") and part (a) "describe a CW decomposition" have no formal content. The polygon quotient is the CW structure.

### t97A05

Evidence: conclusion `IsConnected ((Set.range iW)ᶜ : Set Y)`, with hypothesis `hintersection : HasIntersectionNumber volW volZ volX (iY.comp iW) iZ value` and `hvalue : value ≠ 0`. `HasIntersectionNumber` (ConstructionTargets/ManifoldIntersectionTargets.lean) is concrete: ∃ smooth g′ homotopic to iZ, transverse to W → X, with an explicit finite enumeration of the coincidences and the sum of `localSign`s equal to value. `localSign` compares volX on the concatenated image frame against volW·volZ on the standard frames, so the source orientations are accounted for. The existential in the hypothesis is harmless because the signed count is homotopy invariant for compact W and Z. The hypothesis does not give away the conclusion. One still has to show that a separating connected W bounds a compact region, and therefore has intersection number 0. Orientation via nowhere-zero top forms is a sound encoding.

### t97J02

Evidence: five conjuncts. Existence is `Nonempty (CoverWitness false 12 5)`, `(true 7 6)`, `(false 14 6)`, where a witness is a map from the concrete polygon surface with `IsCoveringMap` and every fibre of `Nat.card` exactly n. Classification is ∀ E compact connected T2 smooth 2-manifold with an n-fold cover → E ≃ₜ the listed surfaces. Answers check: χ(N₄) = −2. A 5-fold cover has χ = −10, and it must be nonorientable because an odd-degree cover of a nonorientable surface cannot be orientable, so it is N₁₂. A 6-fold cover has χ = −12, giving Σ₇ or N₁₄. Both "show they are coverings" and "no other covers" are encoded, as the problem requires.

### t97J07

Evidence: the only open conjunct is `{p | t97J07Map p = p} = t97J07FixedLine ∪ {t97J07IsolatedPoint}`. Every other conjunct is already proved in the file, using definitions that fix their own values. `t97J07LineContribution := 2 * t97J07IndexFromDet t97J07LineNormalDet`, so the factor 2 standing for χ(fixed line) is written in. The final conjunct `t97J07LineContribution + t97J07IndexFromDet t97J07PointDet = 3` is 2·1 + 1 = 3, and nothing relates it to the homology of `ℙ ℂ (Fin 3 → ℂ)` or to the Lefschetz theorem. The chart-conjugacy conjuncts (`LineChart_map`, `PointChart_map`) do tie the local representatives 3u and w/3 to the actual projectivized map. So (b)'s derivative data is honest, apart from the hard-coded χ(CP¹) = 2. A faithful (c) would add `eulerChar (ℙ ℂ (Fin 3 → ℂ)) = 3` via singular homology, or a Lefschetz-number statement about the actual map.

### t98A03

Evidence: `¬IsTopologicalManifold X ∧ Nonempty (FundamentalGroup X x₀ ≃* Monoid.Coprod (Multiplicative (ℤ×ℤ)) (Multiplicative (ZMod 2))) ∧ (∃ C, ConnectedThreeFold C ∧ IsRegularCover C) ∧ (∃ C, ConnectedThreeFold C ∧ ¬IsRegularCover C)`. `IsTopologicalManifold` = T2 ∧ ∃ n and a C⁰ Euclidean atlas, so the negation covers every dimension. `IsRegularCover` = deck homeomorphisms act transitively on each fibre, the standard definition. Answers check: (c) comes from π₁ → ℤ/3 through the ℤ² factor. (d): a ↦ (123), b ↦ 1, c ↦ (12) maps onto S₃, and a point stabiliser is a non-normal subgroup of index 3, so an irregular 3-fold cover exists. The basepoints t₀, r₀ are arbitrary, which is harmless because both spaces are homogeneous.

### t98J01

Evidence: `HasLefschetzNumber T98J01.h 8 ∧ ¬ ContinuousMap.Homotopic T98J01.h (ContinuousMap.id _)`. `HasLefschetzNumber` (ConstructionTargets/RationalLefschetz.lean) is the actual alternating trace of the induced maps on singular homology over ℚ, with no supplied ranks. Maps: rotation (x,y,z) ↦ (−x,−y,z) is the half-turn about the z-axis; reflection (x,y) ↦ (−x,y) is reflection in the y-axis. Value check: L(f) = 1 + 1 = 2 (degree 1), L(g) = 1 − (−1) = 2, and L is multiplicative, so L(h) = 8. L(id) = χ = 0 ≠ 8, so h is not homotopic to id.

### t99A01

Evidence: the six conjuncts are about `PresentedGroup (rels {2})`, `{2,4}`, `{2,4,5}` and `AddMonoidHom.ker boundaryX/Y/Z`, where `boundaryZ v = 2v₀ + 4v₁ + 5v₂`, and so on. The header says: "the topological comparison step is NOT encoded … H₀ = ℤ, the cokernel calculations for H₁, and vanishing of higher cellular groups are omitted". The algebra is correct: π₁ = ℤ/2, ℤ/2, 1 and H₂ = 0, ℤ, ℤ². But the spaces X, Y, Z are never built, and the H₁ answers (ℤ/2, ℤ/2, 0) are not stated. Mathlib's lack of cell-attachment API is not a problem-statement defect. Sibling bundles (t00J07, t98A03) build adjunction quotients and state singular homology directly, so a faithful encoding is available.

### t99A04

Evidence: `(∫ x in 0..1, deriv g x) = 0 ∧ ∀ c, (∫ _x in 0..1, c) = c` under `hloop : g 1 = g 0` plus FTC regularity. Neither conjunct mentions a manifold, a form or separation. The header says so: "the separating surface assertion is NOT encoded as a proxy". The intended answers (period 0 for separating curves on a closed surface; any real value for nonseparating curves, e.g. dx on the torus) are not stated.

### t99J04

Evidence: conjunct 1 is `LinearIndependent ℝ (fun i ↦ fromTangentSpace ∘L mfderiv … (f i) x) → IsLocalDiffeomorphAt … (apm_t99J04_coordinateMap f) x`, which is exactly "f¹…fⁿ form local coordinates near x". Conjunct 2 is as stated, with `[Nonempty X]`, `[T2Space Y]`, `[ConnectedSpace Y]`. Hausdorffness of Y is the usual manifold convention and is needed: S¹ onto one copy in a circle with a doubled point is a counterexample without it. Both manifolds are boundaryless (`modelWithCornersSelf`). The bridge theorems are sorry proof steps only.

### tunk01

Evidence: `(hPresentation : Nonempty (X ≃ₜ apm_tunk01_PolygonSurface)) → … ∧ Nonempty (X ≃ₜ apm_tunk01_N6)`. This is equivalent to PolygonSurface ≃ₜ N₆. `apm_tunk01_PolygonRel` is textually identical to t94J09's (diffed after renaming), and I checked that one against the word by hand. Unlike t94J09, it does not state homology. The problem asks only to classify, so that is not a loss.


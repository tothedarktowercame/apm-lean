# Fidelity grades — open list 1

Grader: read-only; nothing built, run or edited in `/home/joe/code/apm-lean`. Rows and notes appended per problem as finished.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00A02 | faithful | `apm_t00a02` (lowercase a; no `apm_t00A02`) | (a) connected 10-fold covers of a genus-5 surface are homeomorphic, (b)(i) antipodal S²→RP² is a 2-fold cover, (b)(ii) connected regular and non-regular 4-fold covers of RP²∨RP² exist; connectedness of the covers was added | yes: (a) is false without connectedness |
| t00J02 | faithful | `apm_t00j02` (lowercase j) | A smooth self-map of a genus-2 surface, transverse to an embedded smooth circle that is nonzero in H₁, with every component of the preimage bounding an embedded disk, has degree 0 (degree read off the real H₂ map) | no |
| t01A01 | faithful | `apm_t01a01` (lowercase a) | A non-surjective continuous self-map of RP² (the real projectivization with quotient topology) is trivial on π₁ at every basepoint and is homotopic to a constant | no |
| t01A05 | false | `apm_t01a05` (lowercase a) | The existential orientation `∃ ot : T01A05Orientation n Xtilde` needs H_n(X̃) ≅ ℤ, which fails for a disconnected cover (trivial 2-sheeted cover X ⊔ X → X, or n = 0 with k ≥ 2). Part (c) is also dropped and (b) is replaced by the fundamental-class relation | partial: forms, integration and intersection numbers have no Mathlib API; that explains the (b) substitution but not the falsity or dropping (c) |
| t01J04 | narrower | `apm_t01j04` (lowercase j) | The conclusion only asks for *some* smooth half-space atlas on the subspace f⁻¹(cl V). Nothing ties it to X's smooth structure, so "smooth submanifold with boundary of X" is weakened to "topological manifold with boundary that admits a smooth structure". The added T2/Regular hypotheses are harmless | no (the added Hausdorff/regularity hypotheses are justified by Mathlib conventions, but they do not cause the weakening) |
| t02A04 | faithful | `apm_t02a04` (lowercase a) | The explicit quotient of (D²×S¹) ⊔ D² gluing ∂D² along z ↦ (z, z²), the simple (1,2) curve on the boundary torus; every continuous self-map has a fixed point | no |
| t02A08 | narrower | `apm_t02a08` | Z is repaired to S¹×{q}, which is justified. But `HasOrientedIntersection` *defines* the intersection number as deg(pr₂∘f), so the requested computation of I(f,Z) is built into the definition, leaving only "S² has self-maps of every degree n" | yes: I(f,{p}×S²) is undefined (2+2 ≠ 3), so some replacement of Z is forced. The degree-of-projection surrogate is not forced by that defect |
| t03J03 | faithful | `apm_t03j03` (lowercase j) | On the genuine polygon quotient N₃: 7 connected double covers up to equivalence (one Σ₂, six N₄), disconnected ones are trivial, and every embedded cylinder lifts to an orientable double cover | no |
| t91J03 | faithful | `apm_t91j03` (lowercase j) | An embedded circle in Circle × [0,1] has winding number (real H₁ map of the projection to S¹) of absolute value ≠ 2 | no |
| t92J05 | faithful | `apm_t92j05` (lowercase j) | π₁(RP²) ≃ ℤ/2, π₁(S²×S¹) ≃ ℤ at every basepoint, and π₁ of any closed smooth surface with genus-2 homology ≃ ⟨a₁,b₁,a₂,b₂ ∣ [a₁,b₁][a₂,b₂]⟩ | no |
| t93A03 | vacuous | `apm_t93a03` (lowercase a) | The hypothesis `hspine : T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine` is false for the genuine connected sum: it has H₂ ≅ ℤ² and H₃ ≅ ℤ, while S¹∨S¹ has H₂ = H₃ = 0. It would also supply the core of the problem if it held. The first conjunct is only about the spine | no |
| t93J03 | faithful | `apm_t93j03` (lowercase j) | On the genuine aabb polygon quotient: at each basepoint, π₁(K) ≃ ⟨a,b ∣ b⁻¹aba⟩, and every path-connected, locally path-connected, semilocally simply connected subspace whose π₁-image lies in ⟨a⟩ embeds in ℝ² | no |
| t94A01 | faithful | `apm_t94a01` (lowercase a) | For the product topology on ℕ → [0,1], U is open iff it is open for the balls of ρ(f,g) = Σ 2^{-(i+1)}|fᵢ−gᵢ|; reindexing from 1 to 0 keeps the weights | no |
| t94A06 | false | `apm_t94a06` | The model space `E` is an arbitrary normed space, so X can be an infinite-dimensional separable Hilbert manifold, where Sard fails (Kupka 1965): the a.e.-transversality conjunct is then false | no (finite-dimensionality is the standard convention; the encoding dropped it) |
| t94A09 | faithful | `apm_t94a09` (lowercase a) | No smooth nowhere-zero tangent field on S², one exists on S³, and one exists on S¹×S¹ with exactly one zero. Fields are ambient-smooth restrictions orthogonal to the radius | no |
| t94J07 | narrower | `apm_t94j07` (lowercase j) | Only the special case X = Y = S¹ (ambient-smooth circle maps, a 1-form on ℝ², the standard parametrised line integral). General compact boundaryless X, Y and forms of any degree are dropped | no (the reason given is that Mathlib lacks manifold integration, not a problem.md defect) |
| t94J11 | faithful | `apm_t94j11` (lowercase j) | For a setoid whose quotient map (coinduced topology) is open, the graph {(x,y) ∣ x ∼ y} is closed ↔ the quotient is T2 | no |
| t95J05 | false | `apm_t95j05` (lowercase j) | Integration uses Mathlib's unnormalised `hausdorffMeasure 3` on the Euclidean S³, which is (2³/ω₃)·σ = (6/π)·σ. The encoded integral is therefore ½·(−4)·(6/π)(π²/2) = −6π, not the stated −π² | yes, minor: the hint's vol B⁴ = π⁴/2 is a typo for π²/2, and the header repairs it correctly |
| t96A02 | faithful | `apm_t96a02` (lowercase a) | Every continuous self-map of the genuine wedge RP² ∨ RP² (disk quotients with word aa, joined at their centre points) has a fixed point | no |
| t96A06 | faithful | `apm_t96a06` (lowercase a) | There is a continuous f̄ on RP³ (quotient topology) that commutes with the given quadratic map on every nonzero vector, has rational-homology Lefschetz number −3, and is not homotopic to id | no |
| t96J01 | faithful | `apm_t96j01` (lowercase j) | For compact X, T2 Y, continuous surjective f, and closed A, B with f(A) ∩ f(B) = ∅, there is a continuous g : Y → [0,1] that is 0 on f(A) and 1 on f(B) | no |
| t96J06 | faithful | `apm_t96j06` (lowercase j) | RP¹×RP¹ ⊂ RP²×RP² (real projectivizations) is not the manifold boundary of any compact subset W that carries a smooth half-space 3-atlas | no |
| t97A04 | faithful | `apm_t97a04` (lowercase a) | For L̄(x,y) = (2x+y, y−x) on (ℝ/ℤ)²: identity on H₀, matrix [[2,1],[−1,1]] on H₁, degree 3 on H₂ (actual singular maps under some isomorphisms), Lefschetz number 1 − 3 + 3 = 1 | no ("degree of L" read as degree of L̄, which the surrounding text forces) |
| t97A07 | faithful | `apm_t97a07` (lowercase a) | For a nonempty, compact, connected, second-countable T2 smooth X and smooth f : X → ℝⁿ: the critical values are compact, nonempty for n > 0 (empty for n = 0), and infinite when n > 1 and f is nonconstant | yes: (a)'s nonemptiness is false for n = 0 (every map to ℝ⁰ is a submersion), so the n > 0 guard is forced |
| t97J05 | narrower | `apm_t97j05` (lowercase j) | (a) df_p and surjectivity, (b) the explicit parametrisation, and (c) the local normal form are all faithful. But `apm_t97J05_IsSmoothSubmanifold` only asks for a 1-dimensional atlas whose inclusion is smooth and a topological embedding, with no immersion condition. A curve with a corner such as {y = |x|} satisfies it, so "W is a manifold" is weakened | yes: in (c), φ is printed with domain in ℝ² but evaluated at (x,y,z), and the ℝ³ repair is forced. That does not bear on the (b) weakening |
| t98A02 | faithful | `apm_t98a02` (lowercase a) | For closed, smooth, path-connected 4-manifolds with H₄ ≅ ℤ, the genuine quotient connected sum Y has H₀ ≅ ℤ, Hₖ ≅ Hₖ(X₁)×Hₖ(X₂) for 1 ≤ k ≤ 3, H₄ ≅ ℤ, and Hₖ = 0 for k ≥ 5. Caveat: φᵢ are arbitrary topological embeddings, not the tame simplex the source allows | yes, mild: "connected oriented 4-manifolds" omits "closed", which the supplied H₄ fact and the answer need |
| t98A06 | faithful | `apm_t98a06` (lowercase a) | (a) Every smooth vector field lifts through a submersion between finite-dimensional, T2, second-countable manifolds (real tangent-bundle sections and mfderiv). (b) For compact boundaryless X and a submersion f : X → S¹, the fibres over 1 and −1, with the constructed regular-fibre atlases, are diffeomorphic | no |
| t98J06 | faithful | `apm_t98j06` (lowercase j) | If the graph of f is transverse to the diagonal, then at each fixed point df_p − I is bijective and the local sign is sign det(df_p − I). The sign is defined with the diagonal first (the Guillemin–Pollack L = I(Δ, graph f) convention) | ambiguous: read literally ("F transverse to Δ", orientation number of F), the graph-first ordering gives sign det(I − df_p) = (−1)ⁿ·sign det(df_p − I), so the printed claim fails for odd n. The encoding takes the convention under which the claim holds |
| t99A03 | narrower | `apm_t99a03` (lowercase a) | Only the general lemma "a non-identity deck transformation of a connected cover has no fixed point" is stated. (a) (the RP² wedge; answer: yes) is dropped. (b) never mentions #⁴RP² and never produces the fixed-point-free self-map | no (the header says the omissions are due to missing Mathlib infrastructure, not a problem.md defect) |
| t99J03 | false | `apm_t99j03` (lowercase j) | `apm_t99J03_Surface true 0` is the bare closed disk (no edge relations when genus = 0), so S² matches no normal form and the disjunction fails for X = S². Also the χ clause is a tautology about the label, so (c) is not really stated, and (b) is not encoded | no |
| t99J06 | faithful | `apm_t99j06` (lowercase j) | dα = (2z+1) dx∧dy∧dz via Mathlib `extDeriv`, and ∫_C α = 9π/2 via the parametrised cone (image = C, injective and immersive on the interior, ∫dx∧dy > 0). The literal dz∧dz term is kept, and it vanishes | ambiguous: "2yz dz∧dz" is probably a typo (dz∧dx?). The literal reading is well-defined and encoded as printed |
| tunk03 | faithful | `apm_tunk03` (lowercase u) | If `Quotient.mk'` is an open map for the quotient topology, then the relation is closed in X×X ↔ the quotient is T2 | no |

## Evidence notes

### t00A02 — faithful (with a justified repair)
Declaration is `theorem apm_t00a02` (lower-case `a`); there is no `apm_t00A02`. It is proved from two `sorry` bridges (`apm_t00A02_bridge_antipodalCover_isCoveringMap`, `apm_t00A02_bridge_global_cover_classification_and_wedge`), but the statement itself uses no opaque/sorry defs.
- (a) `[T2Space F] [CompactSpace F] [PathConnectedSpace F] [ChartedSpace apm_t00A02_E2 F] [IsManifold apm_t00A02_I2 ⊤ F]` with `apm_t00A02_hasGenusFiveHomology F` (H₀≅ℤ, H₁≅ℤ¹⁰, H₂≅ℤ, Hₖ=0 for k≥3, real singular homology). Among closed surfaces these homology groups pick out exactly the orientable genus-5 surface (non-orientable ones have H₂=0), and every surface is smoothable, so this encodes "closed orientable genus 5". The covers are `[PathConnectedSpace E₁]`, `[PathConnectedSpace E₂]`, and `apm_t00A02_isNfoldCover 10 p` = `IsCoveringMap p ∧ ∀ b, Nat.card {e // p e = b} = n`. Conclusion `Nonempty (E₁ ≃ₜ E₂)`.
- (b)(i) `apm_t00A02_isNfoldCover 2 apm_t00A02_antipodalCover`, where RP² is the genuine quotient of S² by x ~ -x. Exhibiting the standard double cover is a fair reading of "find".
- (b)(ii) For each base point r₀, `Nonempty (apm_t00A02_coverWitness (apm_t00A02_wedge r₀) 4 true)` and `... 4 false`. The witness carries a connected total space, a 4-fold cover, and regularity or its negation. Regularity is deck-group transitivity on fibres (`apm_t00A02_isRegularCover`). The statement is true: π₁ = ℤ/2*ℤ/2 (infinite dihedral) has both normal and non-normal index-4 subgroups. "Draw ... indicating why" is rendered as existence, which is the usual reading.
- PRELIM-DEFECT: (a) says "all 10-fold coverings", which is false for disconnected covers (e.g. two components of degrees 1+9 versus 10 copies of F). The header "Statement repairs" states this, and adding connectedness is the standard intended reading.

### t00J02 — faithful
Declaration is `theorem apm_t00j02` (lower-case `j`); there is no `apm_t00J02`. The proof goes through `apm_t00J02_bridge_1`, which contains a `sorry`. The statement itself uses no opaque/sorry defs.
- Surface: `[T2Space S] [CompactSpace S] [PathConnectedSpace S] [ChartedSpace apm_t00j02_E2 S] [IsManifold apm_t00j02_I2 ∞ S]` with `apm_t00j02_hasGenusTwo` (singular H₁ ≅ ℤ⁴, H₂ ≅ ℤ, higher groups zero). This picks out the closed orientable genus-2 surface.
- `f : C(S,S)` with `ContMDiff … ∞ f`. The curve is `c : C(Circle,S)` with `Topology.IsEmbedding c` and `ContMDiff (𝓡 1) … ∞ c`.
- "Wraps around a handle" is encoded as `apm_t00j02_wrapsHandle c := apm_t00j02_homologyMap 1 c ≠ 0`. This is weaker than "is a handle meridian", so the theorem covers every homologically essential simple closed curve. The statement stays true: pull back the Poincaré dual of [C]. Since f*PD[C] = PD[f⁻¹C] = 0, d·PD[C] = 0 in torsion-free H¹, so d = 0. That makes this a harmless generalisation, not a change of problem.
- Transversality: `∀ x z, f x = c z → range (mfderiv f x) ⊔ range (mfderiv c z) = ⊤`. This is the standard definition.
- Disk hypothesis: `ConstructionTargets.DiskBoundaryHomology.ComponentsBoundByDisks (f ⁻¹' range c)` = `∀ x ∈ s, ∃ d : Disk → X, Continuous d ∧ IsEmbedding d ∧ range (d ∘ circleToDisk) = connectedComponentIn s x`. This is exactly "every component bounds an embedded disk".
- Degree: `apm_t00j02_hasDegree f degree := ∃ e : H₂ S ≅ ℤ, ∀ x, e.hom (f_* x) = degree * e.hom x`. This is satisfiable, and it determines `degree` regardless of the sign of `e`. The conclusion `degree = 0` is therefore the real degree.
- Minor: `c` is not required to be an immersion. That only strengthens the hypothesis set slightly, and the duality argument is topological, so it is not a fidelity concern.

### t01A01 — faithful
Declaration is `theorem apm_t01a01` (lower-case `a`). The body is `sorry` via `apm_t01A01_bridge_1`. `apm_t01A01_RP2 := Projectivization ℝ (Fin 3 → ℝ)` carries the quotient topology. Statement:
```lean
∀ f : C(apm_t01A01_RP2, apm_t01A01_RP2), ¬Function.Surjective f →
  (∀ (x) (γ : FundamentalGroup apm_t01A01_RP2 x), FundamentalGroup.map f x γ = 1) ∧
  ∃ p, ContinuousMap.Homotopic f (ContinuousMap.const _ p)
```
Both requested conclusions are there, and triviality of f_* is asserted at every basepoint.

### t01A05 — false
Declaration is `theorem apm_t01a05` (lower-case `a`); the body is `sorry`. `T01A05Orientation n X` is a structure holding `topIso : H_n(X;ℤ) ≅ ℤ`. The general conjunct reads:
```lean
∀ (n k) (hk : 0 < k) (X Xtilde : Type) [T2/Compact/ChartedSpace/IsManifold on both] (π : C(Xtilde, X)),
  t01A05IsKSheetedCover k π → ∀ o : T01A05Orientation n X,
    ∃ ot : T01A05Orientation n Xtilde, t01A05FundamentalClassRelation (k := k) π ot o
```
The covering space is not required to be connected. The orientation upstairs is existential, and it requires H_n(X̃) ≅ ℤ.
- Counterexample: X = S¹ (n = 1) or the torus (n = 2), X̃ = X ⊔ X, π = the fold map, k = 2. X has an orientation `o`, and π is a 2-sheeted covering map. H_n(X̃) ≅ ℤ² ≇ ℤ, so no `ot` exists and the conclusion fails. For n = 0 the same happens: X = pt, X̃ = k points, k ≥ 2.
- The source takes X̃ as *given* oriented. Encoding its orientation as a hypothesis, or allowing a multi-component fundamental class, would avoid this.
- Also narrower even if the falsity is fixed. Part (b) (∫ π*ω = k∫ω) is replaced by π_*[X̃] = k[X]; the header calls this a "reviewer-directed repair" because Mathlib has no manifold integration. Part (c) (preimages are oriented submanifolds and I(Z̃₁,Z̃₂) = k·I(Z₁,Z₂)) is dropped entirely ("explicitly deferred"). In (a), k > 0 is a reasonable restriction.
- (a) conjunct: the torus cover `(x,y) ↦ (k•x, y)` on `AddCircle 1 × AddCircle 1` plus the fundamental-class relation. This conjunct is true.

### t01J04 — narrower (weakened conclusion)
Declaration is `theorem apm_t01j04` (lower-case `j`); the body is `sorry`. Hypotheses: `n m`, and X and Y are `T2Space`, `ChartedSpace (EuclideanSpace ℝ (Fin n/m))`, `IsManifold … ⊤`, `BoundarylessManifold`, with `[RegularSpace Y]`; `hf : ContMDiff … ⊤ f`, `hU : U ∈ nhds y`. Conclusion:
```lean
∃ V, V ∈ nhds y ∧ closure V ⊆ U ∧
  apm_t01J04_IsSmoothManifoldWithBoundary n {x : X // x ∈ f ⁻¹' closure V}
```
where
```lean
def apm_t01J04_IsSmoothManifoldWithBoundary (n) (S) [TopologicalSpace S] : Prop :=
  (n = 0 ∧ ∃ charts : ChartedSpace (apm_t01J04_Euclidean n) S, … IsManifold … ⊤ S) ∨
  (∃ hn : NeZero n, ∃ charts : ChartedSpace (EuclideanHalfSpace n) S, … IsManifold (modelWithCornersEuclideanHalfSpace n) ⊤ S)
```
The atlas is existentially chosen, and nothing requires its charts to be smooth for, or compatible with, X's structure; the inclusion into X need not be smooth. So the conclusion says "f⁻¹(cl V) is a topological n-manifold with boundary that carries some smooth structure". The source (Guillemin–Pollack) means a smooth manifold with boundary inside X, obtained from a regular value of |f − y|² in a chart via Sard. The topological core is still there, and the statement is true; what is dropped is the smooth compatibility with X.
- `[RegularSpace Y]` is redundant for a T2 finite-dimensional manifold, which is locally compact Hausdorff. Its presence is harmless.
- The problem is true for arbitrary smooth f by the Sard argument, so the hint's "diffeomorphism" is not a prelim defect that forces anything.

### t02A04 — faithful
Declaration is `theorem apm_t02a04` (lower-case `a`). The proof uses `sorry` bridges; the statement uses no placeholders. `apm_t02a04_X` is the quotient of `Sum (Disk × Circle) Disk` by the relation generated by `inr z ~ inl (z, z^2)` for z ∈ S¹, with the coinduced topology. The attaching curve z ↦ (z, z²) is injective, since the first coordinate is z. It runs once around the meridian and twice around the core circle, which is the curve described ("wraps around the hole two full times"). Statement: `∀ f : apm_t02a04_X → apm_t02a04_X, Continuous f → ∃ x, f x = x`.

### t02A08 — narrower (intersection number replaced by a definitional surrogate)
Declaration is `theorem apm_t02a08 (p : Circle) (q : apm_t02a08_S2) : ∀ n : ℤ, ∃ g : C(S2,S2), apm_t02a08_HasDegree g n ∧ apm_t02a08_HasOrientedIntersection (apm_t02a08_fiberMap p g) (apm_t02a08_Z q) n`.
- `apm_t02a08_Z q := {y | y.2 = q}`, i.e. S¹×{q}; the source has {p}×S². The source Z is 2-dimensional in a 3-manifold and S² is 2-dimensional, so I(f,Z) is not defined. That is a genuine PRELIM-DEFECT, and replacing Z by a complementary-dimensional cycle is reasonable.
- `apm_t02a08_HasOrientedIntersection f Z n := ∃ q, Z = apm_t02a08_Z q ∧ apm_t02a08_HasDegree (apm_t02a08_secondProjection.comp f) n`. The oriented intersection number is *defined* as the degree of the second projection. The file itself proves the intersection clause definitionally (`apm_t02a08_fiberMap_hasOrientedIntersection`). What remains is only "for every n there is a self-map of S² of degree n" (`HasDegree` is real singular H₂). The source's "explain in detail your computation of the intersection number" is exactly the identification I(f, S¹×{q}) = deg(pr₂∘f), and that is assumed, not proved. It is not a placeholder: `HasDegree` is real, and the formula is a true theorem. But the intersection-theoretic content is dropped.
- Also `f` is restricted to the fibre-map shape `(const p).prodMk g`, whose image lies in {p}×S². For an existence claim this is fine.

### t03J03 — faithful
Declaration is `theorem apm_t03j03` (lower-case `j`). `ConstructionTargets.Surfaces.Surface false 3` is the genuine quotient of the closed disk by the crosscap word a₁a₁a₂a₂a₃a₃ (`SurfaceRel`: edges `2j` and `2j+1` identified with the same parameter). `Surface true g` is the standard a b a⁻¹ b⁻¹ word. Conjuncts:
- Euler characteristic arithmetic, plus `Nat.card apm_t03J03_character = 7` (the nonzero characters Fin 3 → ZMod 2).
- `∃ reps : character → connectedDoubleCover N3, (∀ c, ∃! phi, coverEquivalent c (reps phi)) ∧ (∀ phi, if phi = (1,1,1) then reps phi ≃ₜ Σ₂ else reps phi ≃ₜ N₄)`. The labels `phi` are not tied to π₁, but the clause still says exactly 7 classes of connected double covers up to equivalence over X, one with total space Σ₂ and six with N₄. That is the answer to (a) (χ = −2, and only the orientation cover is orientable), with covering maps as data.
- Disconnected two-sheeted covers are equivalent to `Sum.elim id id` on X ⊕ X.
- (b), answered "true": for Y orientable (≃ₜ `Surface true g` for some g) with a 2-fold cover `p`, every `IsEmbedding f : Circle × Icc 0 1 → N3` has a continuous lift. The statement is true: an embedded annulus is a neighbourhood of its core, so the core loop preserves orientation and lies in the orientation-cover subgroup.
- Harmless quirk: `Surface true 0` is the bare disk (with no gluing), so it is admitted as an "orientable surface". No double cover of N₃ is a disk, so this has no effect.

### t91J03 — faithful
Declaration is `theorem apm_t91j03 (gamma : C(Circle, Circle × Icc 0 1)) (hgamma : Topology.IsEmbedding gamma) : ∀ n : ℤ, apm_t91J03_HasWindingNumber gamma n → n.natAbs ≠ 2`. `HasWindingNumber` means that, under some orientation isomorphism `H₁(Circle;ℤ) ≅ ℤ`, the real singular-homology map of `Prod.fst ∘ gamma` is multiplication by n. This is satisfiable for the true winding number, and the sign of the isomorphism is absorbed by `natAbs`. "Cannot wrap twice" is encoded literally as |n| ≠ 2. The stronger truth |n| ≤ 1 is not asked for.

### t92J05 — faithful
Declaration is `theorem apm_t92j05` (lower-case `j`); the body is `sorry`, and bridges 1 and 3 are `sorry`.
- (a) `∀ x : Projectivization ℝ (Fin 3 → ℝ), Nonempty (FundamentalGroup _ x ≃* Multiplicative (ZMod 2))`, with RP² carrying the quotient topology.
- (b) `∀ x : S² × S¹, Nonempty (FundamentalGroup _ x ≃* Multiplicative ℤ)`, where S² and S¹ are metric spheres.
- (c) Any `T2`, `Compact`, `PathConnected`, smooth 2-manifold with H₀=ℤ, H₁=ℤ⁴, H₂=ℤ and higher groups zero. This is exactly the closed orientable genus-2 surface. Its π₁ is claimed ≃* `PresentedGroup {[a₀,a₁][a₂,a₃]}`, the standard presentation.
"Say what the fundamental group is" is rendered as the three isomorphisms, which is the natural encoding.

### t93A03 — vacuous (the hypothesis cannot hold, and it would carry the core if it did)
Declaration is `theorem apm_t93a03 (φ₁ φ₂ : T93A03Disk → T93A03Summand) (hφ₁ : IsEmbedding φ₁) (hφ₂ : IsEmbedding φ₂) (hspine : T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine) : Nonempty (FundamentalGroup T93A03Spine _ ≃* FreeGroup (Fin 2)) ∧ ¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂)`.
- `T93A03ConnectedSum` is a genuine construction: two copies of S¹×S², each with φᵢ(open ball) removed, glued along φ₁(s) ~ φ₂(s). For tamely embedded balls it is the closed orientable 3-manifold (S¹×S²)#(S¹×S²), with H₂ ≅ ℤ² and H₃ ≅ ℤ. `T93A03Spine` is S¹∨S¹, whose H₂ and H₃ vanish. So `hspine` is unsatisfiable, and the second conjunct holds vacuously. (Wild embeddings give no plausible escape: the header describes the spine as a "deformation retraction", which is false for this closed 3-manifold. The correct spine of the *punctured* manifold is S¹∨S¹∨S²∨S².)
- Even if a correct homotopy equivalence were substituted, the hypothesis would supply the main content: the whole problem is showing π₁ ≠ 1, and after the hypothesis all that is left is π₁(S¹∨S¹) ≠ 1. The header says the equivalence is "an explicit hypothesis" "following the reviewer-approved route".
- The first conjunct `π₁(S¹∨S¹) ≃* F₂` is true, but it is not about the connected sum.

### t93J03 — faithful
Declaration is `theorem apm_t93j03` (lower-case `j`); the body is `sorry`. `KleinBottle := Surface false 2`, the genuine disk quotient with word aabb (see `ConstructionTargets/Surfaces.lean`). The relator is `b⁻¹ * a * b * a`, which is equivalent to b⁻¹ab = a⁻¹. Statement:
```lean
∀ k, ∃ e : FundamentalGroup KleinBottle k ≃* PresentedKleinGroup,
  ∀ (X : Set KleinBottle) [PathConnectedSpace X] [LocPathConnectedSpace X],
  SemilocallySimplyConnected X → ∀ (x : X) (hx : ↑x = k),
  (∀ g ∈ (FundamentalGroup.mapOfEq (inclusion X) hx).range, e g ∈ Subgroup.zpowers generatorA) →
  ∃ j : C(X, ℝ × ℝ), Topology.IsEmbedding j
```
- `e` is existential, but ⟨a⟩ is characteristic: it is the kernel of π₁ → H₁/torsion ≅ ℤ. The condition therefore does not depend on which isomorphism is chosen, and the existential cannot be used to weaken (b).
- `SemilocallySimplyConnected` means: small loops in U are null-homotopic in X. That is the standard definition.
- Part (b) is true (lift to the cylinder cover corresponding to ⟨a⟩, which embeds in ℝ²).

### t94A01 — faithful
Declaration is `theorem apm_t94a01 (U : Set (∀ _ : ℕ, Icc 0 1)) : IsOpen U ↔ ∀ f ∈ U, ∃ ε > 0, {g | rho f g < ε} ⊆ U`, with `rho f g = ∑' i, (1/2)^(i+1) * |f i - g i|`. The left side is Mathlib's product topology. The right side is openness in the ρ-metric topology. Reindexing from ℕ₊ to ℕ with weight 2^{-(i+1)} is exact. That ρ is a metric is not asked to be proved, and is implicit.

### t94A06 — false (infinite-dimensional models admitted)
Declaration is `theorem apm_t94a06 {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] … [SecondCountableTopology X] (I : ModelWithCorners ℝ E H) [ChartedSpace H X] [IsManifold I ∞ X] (f : X → E3) (hf : ContMDiff I 𝓘(ℝ,E3) ∞ f) : apm_t94a06_family f 0 = f ∧ ∀ᵐ s : E2, apm_t94a06_IsTransverseToZAxis I (apm_t94a06_family f s)`. The family is f + (s₀, s₁, 0). Transversality means `range (mfderiv I _ h x) ⊔ span{e₂} = ⊤` at every x with h x on the z-axis.
- For finite-dimensional X this is exactly the intended Sard argument (the regular values of pr_{xy}∘f), and it is faithful. Fixing a concrete family is fine, since the problem asks to find one.
- But `E` is unrestricted; there is no `[FiniteDimensional ℝ E]`. Counterexample: E = X = ℓ²(ℕ) × ℝ (separable, so second countable), with the self-model. Kupka (Proc. AMS 16 (1965) 954–957) gives a C^∞ function k : ℓ² → ℝ whose critical values contain [0,1]. Let f(x,y) = (k(x), y, 0). Then f_s meets the z-axis at points with k(x) = −s₀, y = −s₁, and it is transverse there iff dk_x ≠ 0. For every s with −s₀ ∈ [0,1] there is a critical x with k(x) = −s₀, so transversality fails on a set of positive Lebesgue measure.
- The header adds `SecondCountableTopology` to rule out uncountable discrete X, but misses finite-dimensionality. The fix is `[FiniteDimensional ℝ E]`. With it, the grade would be faithful. (Boundary or corners in `I` are also allowed, but that does not break the Sard argument.)

### t94A09 — faithful
Declaration is `theorem apm_t94a09 : (¬∃ V : S2 → E3, SmoothSphereField V ∧ ∀ p, V p ≠ 0) ∧ (∃ V : S3 → E4, SmoothSphereField V ∧ ∀ p, V p ≠ 0) ∧ (∃ V : Circle×Circle → ℂ×ℂ, SmoothTorusField V ∧ ∃! p, V p = 0)`. `SmoothSphereField V := ∃ Vext, ContDiff ℝ ∞ Vext ∧ ∀ p, Vext p = V p ∧ ⟪V p, p⟫ = 0`. That is, V is a restriction of an ambient smooth map, tangent to the sphere. The torus version is componentwise tangent to the two circle factors. The three construct-or-refute answers are the correct ones: (a) does not exist (hairy ball), (b) exists, (c) exists. The last two are already proved in the file. Only (a) is `sorry`.

### t94J07 — narrower (special case S¹ → S¹)
Declaration is `theorem apm_t94j07 (alpha : T94J07Form1) (halpha_smooth) (halpha_closed : t94J07IsClosedOnCircle alpha) (f g : E2 → E2) (hf hg : t94J07IsSmoothCircleMap _) (H) (hH : t94J07IsSmoothCircleHomotopy f g H) : t94J07PullbackCircleIntegral alpha f = t94J07PullbackCircleIntegral alpha g`. The header says: "the source's general compact manifolds are specialized to the concrete case `S¹ → S¹`". The encoding of that special case is honest: real `fderiv`, real interval integral, and a smooth homotopy preserving the unit circle on [0,1]. But the special case is nearly degenerate. `t94J07IsClosedOnCircle` asks `extDeriv alpha x v = 0` on pairs of vectors tangent to S¹. Two tangent vectors to a 1-manifold are dependent, so this holds for *every* alpha, and the closedness hypothesis carries no information. Arbitrary compact boundaryless X, general Y and k-forms are all dropped. Missing Mathlib API is not a PRELIM-DEFECT.

### t94J11 — faithful
Declaration is `theorem apm_t94j11 (X) [TopologicalSpace X] (r : Setoid X) : let quotientTopology := TopologicalSpace.coinduced Quotient.mk' inferInstance; IsOpenMap … Quotient.mk' → (IsClosed {p | r.r p.1 p.2} ↔ T2Space (Quotient r))`. This is exactly the source, with the quotient topology given explicitly.

### t95J05 — false (Hausdorff-measure normalisation)
Declaration is `theorem apm_t95j05 : (∃! η : T95J05ProjectiveThreeForm, t95J05ProjectionPullback η = t95J05InclusionPullback) ∧ (∀ η, … → t95J05Integral η = -Real.pi ^ 2)`.
- Forms on RP³ are represented by antipodally invariant densities on S³. `t95J05InclusionPullback x = (x₂³ − 4x₁)·x₁`, which is correct for ι_n(dx₁…dx₄) = vol_{S³}. The antipode is orientation-preserving on S³ ⊂ ℝ⁴. Under this representation, part (a) reduces to the invariance check, which is the actual content, and it is proved.
- `t95J05Integral η := (1/2) * ∫ x, η.1 x ∂Measure.hausdorffMeasure 3`. In Mathlib, `μH[d]` is *unnormalised*: it is the covering sum of `ediam ^ d`, and `hausdorffMeasure_pi_real` makes it Lebesgue only for the sup metric on `ι → ℝ`. On the Euclidean S³ (the subtype of `EuclideanSpace ℝ (Fin 4)`), μH[3] = (2³/ω₃)·σ = (6/π)·σ, where σ is surface measure and ω₃ = 4π/3. So ∫ x₀² dμH[3] = (6/π)(π²/2) = 3π. The odd term vanishes, so `t95J05Integral η = ½·(−4·3π) = −6π ≠ −π²`. The file's own "missing lemma" `∫ x₀² ∂μH[3] = π²/2` is false for the same reason.
- The fix is to divide by the normalising constant, or to use a normalised surface measure. The answer −π² is the right value mathematically (Stokes: −4·vol B⁴ = −2π², halved).
- PRELIM-DEFECT, minor: the hint's π⁴/2 should be π²/2. The header repairs this correctly; it is not the cause of the falsity.

### t96A02 — faithful
Declaration is `theorem apm_t96a02 : ∀ f : ContinuousMap ProjectivePlaneWedge ProjectivePlaneWedge, ∃ x, f x = x`. `ProjectivePlaneWedge := Wedge (surfacePoint false 1) (surfacePoint false 1)`. Here `Surface false 1` is the closed disk with boundary points e^{iπt} ~ −e^{iπt} identified (RP²). `surfacePoint` is the image of the centre, and `Wedge` is `Sum` modulo `inl x₀ ~ inr y₀`, with the coinduced topology (`ConstructionTargets/PointWedgeQuotient.lean`). Identifying a point of each plane is exactly as in the source; the choice of point is irrelevant by homogeneity.

### t96A06 — faithful
Declaration is `theorem apm_t96a06 : ∃ f : C(RP3, RP3), (∀ v : NonzeroVectors ℝ 3, ∃ hv : polynomialMap v.val ≠ 0, f (quotientMap ℝ 3 v) = quotientMap ℝ 3 ⟨polynomialMap v.val, hv⟩) ∧ HasLefschetzNumber f (-3) ∧ ¬ ContinuousMap.Homotopic f (ContinuousMap.id RP3)`.
- (a) The first clause pins f on every class, since `quotientMap` is surjective. So "f̄ exists" is the descent claim, including that f(v) ≠ 0 for v ≠ 0.
- (b) `HasLefschetzNumber` (`ConstructionTargets/RationalLefschetz.lean`) is the real alternating trace on rational singular homology, with finite-dimensionality and a vanishing bound certified. Check: in complex coordinates f = (z², w²) has degree 4 on S³, and f̄ has degree 4 on H₃(RP³;ℚ) = ℚ, so L = 1 − 4 = −3. The value is correct.
- (c) The answer "no" is stated as `¬ Homotopic f id`. It is correct, since L(id) = χ(RP³) = 0.

### t96J01 — faithful
Declaration is `theorem apm_t96j01 (X Y) [CompactSpace X] [T2Space Y] (f) (hf : Continuous f) (hf_surj) (A B) (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint (f '' A) (f '' B)) : ∃ g : Y → Set.Icc (0:ℝ) 1, Continuous g ∧ (∀ x ∈ A, g (f x) = 0) ∧ (∀ x ∈ B, g (f x) = 1)`. This is a verbatim encoding.

### t96J06 — faithful
Declaration is `theorem apm_t96j06 : ¬apm_t96j06_BoundsThreeManifold apm_t96j06_ProductSubspace`. RP² is `Projectivization ℝ (Fin 3 → ℝ)` with the quotient topology, and RP¹ is the projectivization of the plane {v₂ = 0}. `BoundsThreeManifold T := ∃ W, IsCompact W ∧ ∃ charts : ChartedSpace (EuclideanHalfSpace 3) W, IsManifold (𝓡∂ 3) ⊤ W ∧ Subtype.val '' ((𝓡∂ 3).boundary W) = T`. Nothing requires the atlas to be compatible with any smooth structure on the ambient space. That makes the non-bounding claim *stronger* than the smooth one, and it stays true: with ℤ/2 coefficients, [T] = ∂[W] = 0 in H₂(RP²×RP²), but [T]·[T] = (RP¹·RP¹)² = 1. "Bound" is read as bounding a compact manifold, which is standard.

### t97A04 — faithful
Declaration is `theorem apm_t97a04 : t97A04HasHomologicalData apm_t97a04_Lbar apm_t97a04_matrix 3 1`. `Lbar p = (2•p.1 + p.2, p.2 − p.1)` on `AddCircle 1 × AddCircle 1` is the genuine induced map. `t97A04HasHomologicalData f A degree lefschetz` requires that there exist isomorphisms H₀≅ℤ, H₁≅ℤ², H₂≅ℤ under which the actual singular maps are id, `A.mulVec`, and `degree * ·`, and that `lefschetz = 1 − trace A + degree`. With A = !![2,1;−1,1] (the matrix of L), degree 3 = det, and L(L̄) = 1, all answers are correct. The H₁ basis is existential, so the matrix is determined up to GL₂(ℤ)-conjugacy. That is inherent in "determine the induced homomorphism", and the trace is invariant.

### t97A07 — faithful (with a forced n > 0 guard)
Declaration is `theorem apm_t97a07 (m n) {X} [T2Space X] [SecondCountableTopology X] [Nonempty X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace (E m) X] [IsManifold 𝓘(ℝ,E m) ∞ X] (f) (hf : ContMDiff … ∞ f) : IsCompact (criticalValues f) ∧ (0 < n → (criticalValues f).Nonempty) ∧ (n = 0 → criticalValues f = ∅) ∧ (1 < n → (∃ x y, f x ≠ f y) → (criticalValues f).Infinite)`. `criticalValues f = {y | ∃ x, f x = y ∧ ¬Surjective (mfderiv … f x)}` is the real critical-value set of a boundaryless m-manifold. All clauses are true: for (a), use max of a coordinate, or m < n; for (b), use the hint's argument, since ∂f(X) ⊆ I and ℝⁿ∖I is connected when I is finite. PRELIM-DEFECT: for n = 0 the critical-value set is empty, which the file proves (`T97A07.criticalValues_zero`). So "I is non-empty" needs n ≥ 1, and ℝⁿ with n ≥ 1 is the presumable intent.

### t97J05 — narrower (the submanifold predicate lacks an immersion condition)
Declaration is `theorem apm_t97j05`, with six conjuncts:
- (a) `∀ h, fderiv ℝ f p h = (−e·h₁, h₀ + h₂)`, and `Surjective (fderiv ℝ f p)`. Both are correct for f = (eˣ cos y, xz) at p = (1, π/2, 1).
- (b) `apm_t97J05_IsSmoothSubmanifold apm_t97J05_W`, where `IsSmoothSubmanifold s := ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin 1)) s, IsManifold 𝓘 ⊤ s ∧ ContMDiff … (Subtype.val) ∧ Topology.IsEmbedding Subtype.val`. The answer "yes" is right: (0,1) is a regular value on all of W. But the predicate does not require the inclusion to be an immersion. The graph {(x,|x|)} satisfies it: take the global chart parametrised by t ↦ (sgn t·e^{−1/t²}, e^{−1/t²}), which is a C^∞ homeomorphism onto the graph. So the predicate says less than "W is an embedded submanifold". The fix is to add injectivity of `mfderiv` of `Subtype.val`.
- (b) parametrisation: `ContDiffOn ℝ ∞ gamma (Ioo (1/2) (3/2))` and `BijOn gamma (Ioo (1/2) (3/2)) parameterTarget`, where gamma t = (t, π/2, 1/t). This is a genuine explicit local parametrisation near p; the target is W ∩ {q₀ ∈ (1/2,3/2), q₁ ∈ (0,π)}.
- (c) Smooth `OpenPartialHomeomorph`s φ (ℝ³→ℝ³, 0 ↦ p) and ψ (ℝ²→ℝ², (0,1) ↦ 0), each with smooth inverse, such that ψ∘f∘φ = (q₀, q₁) on φ.source. The answer "yes" is correct (local submersion theorem).
- PRELIM-DEFECT: in (c), φ's domain is printed as ℝ² but evaluated at (x,y,z). Correcting it to ℝ³ is forced and faithful.

### t98A02 — faithful (with a tameness caveat)
Declaration is `theorem apm_t98a02 : ∀ X₁ X₂ [T2, Compact, PathConnected, ChartedSpace E4, IsManifold 𝓘 ⊤] (φ₁ φ₂ : Disk⁴ → Xᵢ), IsEmbedding φ₁ → IsEmbedding φ₂ → Nonempty (H₄ X₁ ≅ ℤ) → Nonempty (H₄ X₂ ≅ ℤ) → let Y := T98A02ConnectedSum φ₁ φ₂; H₀ Y ≅ ℤ ∧ (∀ k, 1 ≤ k ≤ 3 → Hₖ Y ≅ Hₖ X₁ × Hₖ X₂) ∧ H₄ Y ≅ ℤ ∧ ∀ k ≥ 5, IsZero (Hₖ Y)`.
- Y is the genuine quotient: punctured summands glued along φ₁(s) ~ φ₂(s). Orientability enters as the H₄ ≅ ℤ hypotheses, which is the fact the source supplies. The answer is the standard one for closed orientable 4-manifolds.
- PRELIM-DEFECT (mild): the source omits "closed", but its supplied fact concerns closed manifolds, and so does the intended answer (H₄(Y) ≅ ℤ). The header adds compactness.
- Caveat, not verified either way: the source allows assuming φᵢ(D⁴) is a simplex of a triangulation, i.e. a tame, collared ball. The Lean statement allows any `Topology.IsEmbedding`, including possible crumpled or wild balls, where the complement may have no collar. For those, the Mayer–Vietoris computation is not immediate. For tame embeddings the statement is exactly the source. If wild balls broke it, the statement would be false rather than faithful; adding tameness (e.g. φᵢ extends to an embedding of a larger ball) would remove the question.

### t98A06 — faithful
Declaration is `theorem apm_t98a06`.
- (a) `∀ n m X Y [T2, SecondCountable, ChartedSpace (E n/m), IsManifold (𝓡 n/m) ∞] f, ContMDiff … f → (∀ x, Surjective (mfderiv f x)) → ∀ v, SmoothVectorField v → ∃ w, SmoothVectorField w ∧ ∀ x, mfderiv f x (w x) = v (f x)`. `SmoothVectorField v` means v is a `ContMDiff` section into the actual `TangentBundle`.
- (b) For compact, T2, second-countable, boundaryless (𝓡 n) X and a smooth submersion f : X → Circle, the fibres `{x // f x = 1}` and `{x // f x = -1}`, with the atlas `ConstructionTargets.ManifoldTargetRegularFiberGlobalAtlas.chartedSpace`, are `Diffeomorph` over the fibre model. That atlas is built from genuine regular-fibre charts; there is no `sorry` or `opaque` in either ConstructionTargets file. The conventions T2 and second countability are made explicit.

### t98J06 — faithful (under the Δ-first sign convention; the problem's convention is ambiguous)
Declaration is `theorem apm_t98j06 (n) [T2, SecondCountable, ChartedSpace (Fin n → ℝ), IsManifold ∞] (horientable : ∃ η : Form (E n) X n, IsVolumeForm η) (f) (hf) (htrans : TransverseGraph f) : ∀ p, f p = p → Bijective (difference f p) ∧ (0 < det (difference f p) → localIntersectionSign f p = 1) ∧ (¬ 0 < det … → localIntersectionSign f p = -1)`.
- `difference f p = mfderiv f p − id` (chart coordinates at p, and f p = p). `TransverseGraph` is range(d graph) ⊔ range(d diag) = ⊤. This part is faithful.
- `localIntersectionSign f p` is the sign of det of `tangentSum (a,b) = dΔ(a) + d graph(b) = (a+b, a+Ab)`, which is det[[I,I],[I,A]] = det(A − I). With the diagonal first, the claimed sign is correct. It is also the Guillemin–Pollack convention L_x(f) = I(Δ, graph f).
- The problem text instead says "F … transverse to the diagonal … orientation number at (p,p)". With the GP definition of I(F, Δ), that would put the graph first, giving det[[I,I],[A,I]] = det(I − A) = (−1)ⁿ det(A − I). Under that reading the printed claim is false for odd n. So problem.md is ambiguous, and the file resolves it by choosing the ordering under which the claim holds. The choice is stated openly in the header. The sign is also a hand-written definition, not a library intersection number. That is acceptable, since it is the definition of the orientation number, but it is where a reviewer should look.

### t99A03 — narrower (both parts effectively dropped)
Declaration is `theorem apm_t99a03 {E B} [ConnectedSpace E] (p : E → B) (hp : IsCoveringMap p) (τ : E ≃ₜ E) (hdeck : p ∘ τ = p) (hne : τ ≠ Homeomorph.refl E) : ∀ x, τ x ≠ x`. This is a true general lemma, but it is not the problem. The header says: "The fixed-point assertion for the fourfold wedge is NOT encoded" and "The identification of the particular double cover of `#³ ℝP²` with `#⁴ ℝP²` is likewise omitted". Neither answer is stated: (a) yes, every self-map of ∨⁴RP² has a fixed point (Lefschetz); (b) no, #⁴RP² has a fixed-point-free self-map (the deck involution of the double cover of #³RP², or a rotation). Missing Mathlib infrastructure is not a PRELIM-DEFECT.

### t99J03 — false (the genus-0 normal form is a disk)
Declaration is `theorem apm_t99j03 : ∀ X [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace E2 X] [IsManifold 𝓘 ⊤ X], (∃! g, Nonempty (X ≃ₜ apm_t99J03_Surface true g) ∧ χ true g = 2 − 2g) ∨ (∃! k, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k) ∧ χ false k = 2 − k)`.
- `apm_t99J03_SurfaceRel true 0 x y := ∃ j, j < 0 ∧ …` is never satisfied, so `apm_t99J03_Surface true 0` is the closed unit disk with no identifications. It is not the sphere (the standard normal form is aa⁻¹). Counterexample: X = `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`, which carries Mathlib's smooth 2-manifold instance. X is not homeomorphic to the disk: it has no boundary, which can be seen by invariance of domain or by H₂ = ℤ ≠ 0. It is not homeomorphic to any `Surface true g` with g ≥ 1 (H₁ ≠ 0 for those), or to `Surface false k` with k ≥ 1. Both disjuncts fail. (`ConstructionTargets.Surfaces.Surface true 0` has the same defect. In t03J03 it causes no harm; see that note.)
- Even with the genus-0 case fixed, the statement is thin. The conjunct `apm_t99J03_eulerCharacteristic true g = 2 - 2 * g` is true by `rfl` for every g, and it says nothing about X's Euler characteristic. So (c), the classification by χ plus orientability, is not stated. (b), "outline the proof", is not formalisable and is dropped; the header says the polygon construction "records" it. The (a) content, normal forms with uniqueness, is the substantive part.

### t99J06 — faithful (literal reading of a probable typo)
Declaration is `theorem apm_t99j06 : (extDeriv alpha = fun p => (2 * p 2 + 1) • volumeForm) ∧ parametrization '' parameters = cone ∧ InjOn parametrization interiorParameters ∧ (∀ p ∈ interiorParameters, Injective (fderiv ℝ parametrization p)) ∧ 0 < rectangleIntegral (fun _ => coordinateWedge 0 1) parametrization 0 (2π) 0 1 ∧ rectangleIntegral alpha parametrization 0 (2π) 0 1 = 9π/2`.
- `coordinateWedge i j` is the 2×2 determinant of the (i,j) coordinates, i.e. a genuine dxᵢ∧dxⱼ, and `coordinateWedge 2 2 = 0`. `rectangleIntegral` integrates ω(φ)(∂_θφ, ∂_zφ) over [0,2π]×[0,1].
- Checked by hand: dα = (2z+2x) + (1−2x) = (2z+1) dx∧dy∧dz. On the parametrisation ((1−t)cos θ, (1−t)sin θ, t), dx∧dy pulls back to (1−t) > 0, so the orientation is right. ∫α = ∫₀¹ [2π(1−t)(t²+4) + π(1−t)²] dt = 25π/6 + π/3 = 9π/2. Stokes agrees: ∫(2z+1)dV = π/2 over the solid cone, and the base disk contributes −4π, giving π/2 + 4π.
- PRELIM ambiguity: `2yz dz∧dz` is identically zero as printed, and is probably a typo. The literal term is kept, and the header says so. The answer is correct for the literal form.

### tunk03 — faithful
Declaration is `theorem apm_tunk03 {X} [TopologicalSpace X] (s : Setoid X) (hopen : IsOpenMap (Quotient.mk' : X → Quotient s)) : IsClosed {p : X × X | s.r p.1 p.2} ↔ T2Space (Quotient s)`. `Quotient s` carries Mathlib's quotient (coinduced) topology instance. This is the same problem as t94J11, and the encoding is equivalent.

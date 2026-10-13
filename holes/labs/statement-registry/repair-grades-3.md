# Repair grades, batch 3: proposed RevisedMain.lean revisions

Read-only grading. Each `holes/labs/blueprints/<id>/RevisedMain.lean` is compared with `problems/<id>/problem.md`, the current `problems/<id>/lean/Main.lean`, and the triage notes. Nothing was built, so whether the revisions elaborate is not checked here.

| id | current really unfaithful? | revision grade | true? | change | remaining defect |
|---|---|---|---|---|---|
| t97J04 | Yes. It states the invariants of a hand-built T²∨S¹ and never builds T ∪_C M. | faithful | yes | correction | none of substance. Calling edge c the "meridian" is an arbitrary but legitimate choice. |
| t97J05 | Mildly. The old predicate allowed non-immersive charts ("corners"). The statement was true but weak. | faithful | yes | improvement | none |
| t97J07 | Yes, for part (c). That conjunct was only the arithmetic 2+1=3, with no χ(CP²). | faithful | yes | correction (part (c) added) | χ(CP¹)=2 is still hard-coded in the line contribution. Nothing forces χ to be computed via Lefschetz. Both are acceptable. |
| t98A04 | Yes, for part (a). With both atlases existential, it said "a submersion for some smooth structures". | faithful | yes | correction (source half) | none in the statement. Pinning the target is optional (see below). Not built: the ℝ-inner-product and `Fact` instance path on `EuclideanSpace ℂ (Fin 2)` is unverified. |
| t99A01 | Yes. It was a pure-algebra stand-in: no X, Y, Z, and no H₀ or H₁. | faithful | yes | correction | none |

## Evidence

### t97J04
- Current: `apm_t97J04_WedgeRel | base : (.inl (1,1)) ~ (.inr 1)` on `(Circle × Circle) ⊕ Circle`. Its docstring says "The concrete deformation-retract model `T² ∨ S¹`". That is the step the decomposition exists to justify, and the statement assumes it. So the triage verdict "narrower / assumed" stands.
- Revision: `Sum Disk Disk`, with `Disk = closedBall (0:ℂ) 1` and `edgePoint n j t = exp(2πi(j+t)/n)` (`ConstructionTargets/Surfaces.lean:19`).
  - Relations `a,b`: edge 0 ~ edge 2 reversed, edge 1 ~ edge 3 reversed. Relations `c,d`: edge 4 ~ edge 6 reversed, edge 5 ~ edge 7 reversed. This is the word aba⁻¹b⁻¹cdc⁻¹d⁻¹, the same scheme as the library's `SurfaceRel true 2`, so it gives Σ₂.
  - The first four letters give the punctured torus T, the last four give the punctured torus under M, and the common circle C is the octagon diagonal separating them.
  - `meridian t : (.inl (edgePoint 8 4 t)) ~ (.inr (edgePoint 1 0 t))`. Here `edgePoint 1 0` is the full boundary circle exp(2πit), and t=0 and t=1 give the same point. So the second disk is attached along the closed loop c, a nonseparating meridian of M's torus. Hence X = T ∪_C M, as problem.md describes.
- Invariants:
  - π₁ = ⟨a,b,c,d | [a,b][c,d], c⟩ ≅ ⟨a,b,d | [a,b]⟩, which matches `apm_t97J04_relator` on `Fin 3`.
  - Cells: 1 vertex, 4 edges, 2 faces, so χ = −1. The octagon's cellular boundary is 0 and the disk's boundary is c. So H₀=ℤ, H₁=ℤ⁴/⟨c⟩=ℤ³, H₂=ℤ, and H_k=0 for k≥3. All match.
- The basepoint is the octagon centre, which is fine because X is path-connected.
- Part (a) asks for "a presentation". The theorem states the presentation up to isomorphism, which is an acceptable encoding.

### t97J05
- The revision adds `∀ x : s, Function.Injective (mfderiv 𝓘(ℝ,R1) 𝓘(ℝ,R3) Subtype.val x)` to the existing `ContMDiff` and `IsEmbedding` conditions. Since `ContMDiff` holds, mfderiv is the real derivative and not the junk value 0. Smooth plus embedding plus injective differential is exactly "embedded 1-dimensional submanifold".
- The new requirement is true. On W, cos y = 0, so sin y = ±1, and xz = 1, so x ≠ 0. The rows of df are (0, ∓eˣ, 0) and (z, 0, x), which are independent. So (0,1) is a regular value and W is a closed embedded 1-manifold. Charts from the implicit function theorem satisfy every clause. W has infinitely many components (y = π/2 + kπ), but nothing in the statement needs connectedness.
- The rest is unchanged and faithful: the fderiv formula, surjectivity, the γ(t) = (t, π/2, 1/t) bijection onto a neighbourhood of p in W, and the normal form for part (c) on the repaired domain ℝ³.

### t97J07
- Current: the last conjunct `t97J07LineContribution + t97J07IndexFromDet t97J07PointDet = 3` is arithmetic on defined numbers. Part (c) was absent, as triage-3 says.
- Revision: adds `RationalLefschetz.HasEulerCharacteristic T97J07CP2 3`. Its definition (`ConstructionTargets/RationalLefschetz.lean`):
  - every rational singular homology group must be finite-dimensional;
  - there must be a bound beyond which all homology is `Subsingleton`;
  - the value is Σ (−1)^k · trace of the map that `id` induces on H_k(X;ℚ).
- On finite-dimensional spaces the trace of the identity is the dimension. The finiteness clauses stop the trace's junk value on infinite-dimensional modules from faking a value. So this is an honest χ.
- `ProjectiveSpaceTopology.Space ℂ 2` is `Projectivization ℂ (Fin 3 → ℂ)` with the topology coinduced from the nonzero vectors, which is the standard CP². H_*(CP²;ℚ) = ℚ,0,ℚ,0,ℚ, so χ = 3 and the conjunct is TRUE.
- The vector type `Fin (2+1) → ℂ` matches `t97J07Linear`. Every other conjunct is copied unchanged.
- Remaining softness, all acceptable:
  - `t97J07LineContribution := 2 * …` hard-codes χ(CP¹).
  - Lean cannot enforce "use this to compute". Adding `HasLefschetzNumber ⟨t97J07Map, _⟩ 3` would tie the two together, but it is not required.

### t98A04
- Current: `∃ sourceCharts : ChartedSpace R3 S3, ∃ targetCharts …`. With a free source atlas, the statement says less than "the Hopf map is a submersion". You may pick any smooth structure on the topological S³, for example one pulled back through an arbitrary homeomorphism. The revision fixes this by using `Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1` with `Fact (finrank ℝ = 3+1)`, so Mathlib's standard sphere atlas is the source.
- Target still existential. My view: this does NOT weaken part (a), so it is not narrower. With the source atlas fixed, a surjective smooth submersion determines the target's smooth structure. Suppose π : S³ → (CP¹, 𝒜) is a smooth submersion. It then has local smooth sections s_𝒜, and the standard π has local sections s_std. Locally id : (CP¹,std) → (CP¹,𝒜) equals π ∘ s_std, which is smooth; the inverse is π ∘ s_𝒜, also smooth. So the only witnesses 𝒜 are atlases compatible with the standard affine-chart structure. The existential is therefore equivalent to "π is a submersion onto CP¹ with its standard structure", and a proof must in effect build that structure.
  - This argument is stronger than triage-3's appeal to the uniqueness of smooth structures on surfaces only up to diffeomorphism.
  - If a pinned target is still wanted, the natural one is the two affine charts [z₁:z₂] ↦ z₂/z₁ and z₁/z₂ (realified to ℝ²), or a fixed homeomorphism to `Metric.sphere (0:ℝ³) 1` with Mathlib's sphere atlas. This is cosmetic, not a fidelity issue.
- Other conjuncts are unchanged and TRUE:
  - the fibre over [1,0] is `{z | z.1 1 = 0}`;
  - every fibre is `≃ₜ Circle` and equals the unit-scalar orbit;
  - there is no continuous section, with the codomain repaired to S³.

### t99A01
- Current: only `PresentedGroup (rels {2})` and so on, plus kernels of `boundaryX/Y/Z`. No space appears, and H₀ and H₁ are omitted. This is a stand-in, as triage-3 says.
- Revision: `AttachSpace degree` is the quotient of `Circle ⊕ (Fin r × closedBall 0 1)` by `inl (z ^ degree i) ~ inr (i, z)`. Each disk's boundary is attached to the single circle S by z ↦ z^d, a degree-d map, with degrees ![2], ![2,4], ![2,4,5]. These are exactly X, Y and Z, with every cell attached to S as problem.md says.
- Invariants, all TRUE:
  - π₁: X = RP² gives ℤ/2. Y gives ⟨a | a², a⁴⟩ = ℤ/2. Z gives ⟨a | a², a⁴, a⁵⟩ = 1, since gcd = 1.
  - Cellular boundary ∂₂ = (2), (2,4), (2,4,5).
  - X: H₀=ℤ, H₁=ℤ/2, H₂=0.
  - Y: H₀=ℤ, H₁=ℤ/gcd(2,4)=ℤ/2, H₂=ker=ℤ.
  - Z: H₀=ℤ, H₁=0, H₂=ker, which is free of rank 2, so ℤ².
  - H_k = 0 for k ≥ 3 in all three.
- The basepoint is the image of 1 ∈ S, and all three spaces are path-connected.

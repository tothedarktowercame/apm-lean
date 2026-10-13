# Fidelity triage, batch 2

Read-only triage, done against `/home/joe/code/apm-lean` as of 2026-10-13. Nothing was built. None of these nine problems has an entry in `problems/STATEMENTS.json`. `t95J03` appears only under `revoked`. The table was reached independently. Afterwards I compared it with the earlier grades in `open-grades-1.md`, `open-grades-3.md` and `doubt-grades.md`, and it agrees with them wherever they overlap.

| id | class | grade-or-gap | one-line reason |
|---|---|---|---|
| t03J05 | B | (currently FALSE) | Part (b) quantifies over every Mathlib 4-manifold X, and these need not be Hausdorff. Gluing copies of ℝ⁴ onto neighbourhoods of the tori makes two tori null-homotopic, so they are homotopic. Part (a) counts set-theoretic intersection points, which is not an intersection number. Fix: add `[T2Space X]`, and require A₁, B₁ to cross transversally at their single point |
| t93A03 | B | (vacuous) | `hspine : ConnectedSum ≃ₕ S¹∨S¹` cannot hold, because H₂(S¹×S² # S¹×S²) ≅ ℤ² while H₂(S¹∨S¹) = 0. The hypothesis would also carry the whole core if it held. Fix: drop `hspine` and state `¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂)`, optionally with collared (tame) φᵢ |
| t94A06 | B | (currently FALSE) | The model space `E` is an arbitrary normed space. For a Hilbert-space manifold, Sard fails (Kupka 1965), so a.e. transversality fails. Fix: add `[FiniteDimensional ℝ E]`. The translation family itself is a faithful answer |
| t94J07 | C | gap: integration of k-forms on compact oriented manifolds (and Stokes). A narrower statement exists, which is the current one | Specialised to X = Y = S¹. This special case is true and acceptable as a stand-in. Closedness is automatic for 1-forms on S¹, so the case never uses the closed hypothesis. A richer narrower case, a loop in an open U ⊆ ℝⁿ with a closed 1-form on U, is expressible today |
| t95J03 | B | (narrower) | True as encoded, but `Surface true 0` is the closed disk, so S² is missing from the domain. This was already revoked for that reason, and the statement has not changed since. Fix: send `.orientable 0` to `Metric.sphere (0:ℝ³) 1` and drop `.nonorientable 0` |
| t95J05 | B | (currently FALSE) | It integrates against Mathlib's unnormalised `hausdorffMeasure 3`, which is (6/π)·σ on S³, so the encoded value is −6π, not −π². Fix: replace `Measure.hausdorffMeasure 3` with `μHE[3]` (`euclideanHausdorffMeasure`). The descent part and the π⁴→π² hint repair are correct |
| t96A08 | B | (vacuous) | Paths only need to be continuous and smooth off a finite set, so an oscillating path can have a non-integrable ω(γ′). Lean's interval integral then returns 0, and `hindependent` forces ω ≡ 0. Fix: require smoothness on each closed segment between breaks (or add `IntervalIntegrable`). The f : M→ℝ and reachability repairs are correct |
| t97J04 | B | (narrower) | It never builds X = T ∪_C M. It states π₁ ≅ ⟨a,b,d∣[a,b]⟩ and H_* = (ℤ,ℤ³,ℤ,0,…) for a hand-supplied model T²∨S¹. The values are correct, but the step X ≃ T²∨S¹ is assumed in the encoding. Fix: construct X as a quotient (as in t93A03/t02A03) and state the same invariants for it |
| t97J05 | A | narrower-acceptable | Parts (a), (b) parametrisation and (c) are faithful, and the part (c) domain typo ℝ²→ℝ³ is repaired correctly. `IsSmoothSubmanifold` does not require the inclusion to be an immersion, so "W is a manifold" is certified only weakly: curves with corners pass. Small fix: add injectivity of `mfderiv Subtype.val` |

## Evidence notes

### t03J05
- Part (b) conjunct: `∀ (X : Type) [TopologicalSpace X] [ChartedSpace apm_t03J05_E4 X] [IsManifold apm_t03J05_I4 (⊤ : ℕ∞) X] [BoundarylessManifold apm_t03J05_I4 X] (incl : C(F* × F*, X)), Topology.IsOpenEmbedding incl → ∀ i j, i ≠ j → ¬ ContinuousMap.Homotopic (incl.comp (g i)) (incl.comp (g j))`. There is no `T2Space`.
- Counterexample, valid for every witness. Each embedded circle aᵢ in the orientable F* has an annulus neighbourhood. So the torus aᵢ×aᵢ has a neighbourhood Uᵢ ≅ T²×ℝ², which embeds openly in ℝ⁴. Let X be F*×F* with two copies of ℝ⁴ glued along U₁ (around a₁×a₁) and U₂ (around b₁×b₁). X is locally Euclidean, smoothable and connected, but not Hausdorff. Both tori factor through a contractible ℝ⁴, so both are null-homotopic, and therefore g 0 ≃ g 1. The existential is unprovable.
- With `[T2Space X]` the claim is true. A compact surface S ⊂ F*×F* is closed in X, so excision gives H₂(X, X∖S) ≅ H₂(W, W∖S), and the intersection count with S separates the tori.
- Part (a): `Nat.card {p // p ∈ imageIntersection (A₁×A₁) (B₁×B₁)} % 2 = 1`. Two curves that touch tangentially at one point give a count of 1 but intersection number 0. The header's "mod-2 intersection" repair is therefore not what is encoded. Fix: require a chart around the unique point A₁∩B₁ in which A₁ and B₁ are the coordinate axes. That gives a transverse crossing, hence mod-2 intersection number 1 for the products. The conjunct `eulerCharacteristic true 2 = -2` is decoration.

### t93A03
- `theorem apm_t93a03 (φ₁ φ₂) (hφ₁ : IsEmbedding φ₁) (hφ₂ : IsEmbedding φ₂) (hspine : T93A03ConnectedSum φ₁ φ₂ ≃ₕ T93A03Spine) : Nonempty (FundamentalGroup T93A03Spine _ ≃* FreeGroup (Fin 2)) ∧ ¬ SimplyConnectedSpace (T93A03ConnectedSum φ₁ φ₂)`.
- The header's claim that the connected sum "deformation retracts onto its wedge-of-circles spine" is false. Each (S¹×S²)∖ball ≃ S¹∨S², and the sum is a closed 3-manifold with H₂ ≅ ℤ² and H₃ ≅ ℤ. So `hspine` is unsatisfiable, at least for tame balls, and the statement is vacuous. The second conjunct is proved from `hspine` alone (`apm_t93a03_connectedSum_not_simplyConnected_of_piOne_equiv`), so the hypothesis carries the core. The construction of `T93A03ConnectedSum` itself is genuine.
- A faithful statement is expressible today. For example, a covering-space proof via a nontrivial connected cover needs no new library.

### t94A06
- `theorem apm_t94a06 {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] … [SecondCountableTopology X] (I : ModelWithCorners ℝ E H) … : apm_t94a06_family f 0 = f ∧ ∀ᵐ s : E2, apm_t94a06_IsTransverseToZAxis I (apm_t94a06_family f s)`.
- The family `f x + (s₀, s₁, 0)` is a correct answer. f_s meets the axis exactly where (f₀,f₁) = −s, and it is transverse there iff −s is a regular value. So in finite dimensions this is Sard.
- Counterexample: take X = ℓ²×ℓ² and Kupka's C^∞ k : ℓ² → ℝ whose critical values contain [0,1]. Set f(x,y) = (k x, k y, 0). For s in −([0,1]×[0,1]), which has positive measure, f_s is not transverse. Fix: add `[FiniteDimensional ℝ E]`.

### t94J07
- `theorem apm_t94j07 (alpha : T94J07Form1) (halpha_smooth) (halpha_closed : t94J07IsClosedOnCircle alpha) (f g : E2 → E2) (hf hg : t94J07IsSmoothCircleMap _) (H) (hH : t94J07IsSmoothCircleHomotopy f g H) : t94J07PullbackCircleIntegral alpha f = t94J07PullbackCircleIntegral alpha g`.
- The header states the gap: "Mathlib presently has no general integration and Stokes theory for manifold differential forms". The S¹ case is true: the derivative of the slice integral reduces to dα on two parallel tangent vectors, which is 0.
- `t94J07IsClosedOnCircle` evaluates `extDeriv alpha x v` on two vectors tangent to S¹. These are parallel, so the hypothesis always holds. The case is therefore narrower than "closed form". A loop in an open U ⊆ ℝⁿ with a closed 1-form on U would keep closedness meaningful.

### t95J03
- `T95J03SurfaceSpace (.orientable g) = TopCat.of (Surface true g)`. `SurfaceRel true 0` is `∃ j < 0, …`, which is empty, so `Surface true 0` is the closed disk.
- `theorem apm_t95j03 (k) (hk : 1 < k) : {F | T95J03SharesKFoldCover k F t95J03KleinBottle} = if Even k then {torus, Klein} else {Klein}`.
- This is true even though covers are allowed to be disconnected. Each component has χ = d·χ(F). For odd k, some component of any Klein-bottle cover has odd degree and is nonorientable. Only the S² case is missing. Statement unchanged since the 09-28 revocation.

### t95J05
- `def t95J05Integral η := (1 / 2 : ℝ) * ∫ x, η.1 x ∂Measure.hausdorffMeasure 3`, and the target is `-Real.pi ^ 2`.
- The density `(x₂³ − 4x₁)·x₁` is the correct value of i*ω against the outward-oriented volume form. Its integral against surface measure is −4·(2π²/4) = −2π², and half of that is −π².
- Mathlib's `μH[3]` is unnormalised. On Euclidean 3-dimensional sets it equals (2³/ω₃)·σ = (6/π)·σ, so the encoded integral is −6π. The pinned Mathlib has `μHE[d]` (`Geometry/Euclidean/Volume/Measure.lean`). Using it makes −π² correct. Part (a) is fine: the antipode preserves orientation on S³, so its content is the invariance lemma.

### t96A08
- `apm_t96a08_IsPiecewiseSmoothPath I γ := Continuous γ ∧ ∃ breaks : Finset ℝ, ∀ t ∈ Icc 0 1, t ∉ breaks → ContMDiffAt 𝓘(ℝ,ℝ) I ⊤ γ t`, and `LineIntegral := ∫ t in 0..1, ω (γ t) ((mfderiv … γ t) 1)`.
- Suppose ω(p₀)(v) = c ≠ 0 in a chart. Compare the segment γ₁(t) = p₀ + tεv, whose integral is about εc ≠ 0, with γ₂(t) = p₀ + g(t)v. Here g is continuous with g(0) = 0 and g(1) = ε, smooth on (0,1], and ∫|g′| = ∞ (for example t + t·sin(1/t)-type oscillation). Then |ω(γ₂)(γ₂′)| ≥ (c/2)|g′| is not integrable, so the Lean integral is 0.
- So `hindependent` implies ω ≡ 0, and the theorem is vacuous for every nonzero ω. Fix: require `ContMDiffOn` on each closed segment between consecutive breaks, which matches the textbook meaning of piecewise smooth.

### t97J04
- `def apm_t97J04_X := Quotient (EqvGen.setoid apm_t97J04_WedgeRel)` with `base : WedgeRel (.inl (1,1)) (.inr 1)`, which is T²∨S¹. Its docstring calls it "The concrete deformation-retract model `T² ∨ S¹` of the specified finite complex".
- `theorem apm_t97j04 : Nonempty (FundamentalGroup apm_t97J04_X _ ≃* PresentedGroup {[a,b]}) ∧ H 0 ≅ ℤ ∧ H 1 ≅ ℤ³ ∧ H 2 ≅ ℤ ∧ ∀ k ≥ 3, IsZero (H k)`.
- The values are right. X = Σ₂ ∪_c D² ≃ Σ₂/c ≃ T²∨S¹, and χ = −1. But that equivalence is the step the problem's decomposition exists for, and it is assumed. Every ingredient needed to state the invariants of the genuine T ∪_C M is in Mathlib: quotient spaces, `FundamentalGroup`, `singularHomologyFunctor`.

### t97J05
- `fderiv … p h = toLp ![-exp 1 * h 1, h 0 + h 2]` is correct (rows (0,−e,0) and (1,0,1)). The surjectivity conjunct is correct. γ(t) = (t, π/2, 1/t) on (1/2, 3/2) is proved to be a bijection onto an open piece of W around p. The local normal form uses `OpenPartialHomeomorph` with smooth inverses and `ψ (f (φ q)) = (q 0, q 1)`.
- The weak spot is `apm_t97J05_IsSmoothSubmanifold s := ∃ charts : ChartedSpace ℝ¹ s, IsManifold 𝓘 ⊤ s ∧ ContMDiff … Subtype.val ∧ IsEmbedding Subtype.val`. It has no immersion condition, so a corner such as a smooth flat-function parametrisation of y = |x| also qualifies.
- W really is an embedded 1-manifold, because (0,1) is a regular value: x ≠ 0 on W. So the statement is true and acceptable. Adding `∀ x, Function.Injective (mfderiv … Subtype.val x)` makes it faithful.

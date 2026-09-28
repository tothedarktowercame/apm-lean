# Fidelity grades — list 2

Read-only review of `/home/joe/code/apm-lean` (current HEAD). No builds and no lake runs.

| id | grade | one-line reason | repair classification |
|---|---|---|---|
| t00A04 | hypothesis-carries-core | `¬ NullHomotopic id_X` is assumed, which is exactly the noncontractibility of a closed oriented positive-dimensional manifold; what remains is a one-line composition with the retraction | — |
| t00J04 | faithful | ∃ smooth `f` with `ω = df`, `ω p = ω_p`, and chartwise `extDeriv` of the coordinate form of `df` = 0; this answers (b) "yes" and implies (a). It adds `[SecondCountableTopology X]` (conventional) | dfc0a31b: improvement (makes closedness explicit over c64226d7's ∃f, mfderiv f p = ω_p). Net vs bank 4d7b2110: correction (bank used `opaque` smooth/closed/exact predicates) |
| t01A06 | faithful (caveat) | (a) value 2π²Rr² is correct, but the pulled-back integrand is hard-coded rather than derived from ω; (b) nonexistence stated with a real closedness predicate and a periodic smooth loop on T | — |
| t01J03 | faithful | π₁(T²)≅ℤ², H_*(T²); glued space is an actual quotient; the twice-spiral condition (meridian ↦ (1,2)) gives π₁ = ℤ/2 and H = ℤ, ℤ/2, 0, ℤ (RP³) | — (unchanged since bank 082028c1) |
| t02A03 | narrower | X and Y are replaced by their deformation-retract models T² and T²∨S¹; the geometric retraction is never stated, so (a) reduces to π₁(T²) | — |
| t91A01 | hypothesis-carries-core | (b) assumes `∑ index = 2 − 2g` (Poincaré–Hopf plus classification) over an abstract Finset, which leaves only a parity step; (a) z³ is a correct index-3 model | — |
| t91A04 | stronger (mild) | Banach fixed point with `∃!` (uniqueness added); `[Nonempty M]` is a necessary implicit hypothesis | not listed as REPAIRED; 64921b05 replaced a frame file (no `apm_t91a04`, `λ` used as an identifier) → correction |
| t91A07 | narrower (mild) | stated for a smooth `f : E → E` on a finite-dimensional normed space, not a manifold; the local chart reduction is omitted. Bijective(df−id) ⇔ no eigenvalue 1 is correct | — |
| t91J02 | faithful | `¬Nonempty (Circle × Circle ≃ₜ sphere in ℝ³)` | — |
| t92J02 | faithful (no registered theorem) | (a) `IsCompact (f '' K)`; (b) a continuous bijection from a compact space to T2 gives a homeomorphism. **No `theorem apm_t92j02` exists**; the file is still a frame namespace | — |
| t92J07 | faithful (caveat) | common regular value for countably many smooth maps (Sard); "fiber is a submanifold" is encoded as the regular-value certificate, and the preimage theorem is not formalized | fff91b83: correction (bank's conjunct was an `opaque IsSmoothSubmanifold`; formally a conjunct was dropped, but it had no content) |
| t93A02 | faithful | completeness of nonempty closed bounded sets under `hausdorffDist`; nonemptiness is a correct, needed addition | — |
| t94A02 | faithful (no registered theorem) | continuous f : ℝ→ℝ, image ⊆ [0,1], f⁻¹{0}=A, f⁻¹{1}=B. **No `theorem apm_t94a02`**; only `separate_closed_sets` in a frame namespace | — |
| t94J02 | faithful | τ<σ (strictly finer, since Mathlib's ⊥ is discrete) → ¬compact; σ<τ (strictly coarser) → ¬T2 | cb8af566: correction (the 02108503 statement had both orders inverted and was false: X=Bool, σ=⊥, τ=⊤). The listed "bank" 25bcef42 is an empty namespace with no statement |
| t94J06 | faithful | ∃ z, z⁴+5z³+iz³+cos‖z‖ = 0 | — |
| t95A03 | faithful (no registered theorem) | complete plus totally bounded implies CompactSpace (stated for PseudoMetricSpace, mildly more general). **No `theorem apm_t95a03`** | — |
| t95J04 | stronger (benign) | (a) adds the conjuncts μH[n](range f)=0 and nonsurjectivity to null-homotopy, for genuine compact k-manifolds; (b) S⁶, S²×S⁴, S³×S³ are simply connected and pairwise **non-homeomorphic** (stronger than non-diffeomorphic) | 9348ebeb: correction of the bank (78bd777a types and predicates were `def … := by sorry`), but it put the Sard consequence into the `SmoothMap` structure (hypothesis-carries-core for (a)); e7008638: correction (removes that field and uses real `ContMDiff` manifolds) |
| t96J05 | hypothesis-carries-core | `hr`, `hlevel`, `hdata` supply a positive attained regular value r² of ‖x‖² (Sard's output); only the regular-level-set theorem is left | c494d495: correction of a bank that was near-vacuous (its `RegularValue` was trivially true and a hypothesis handed over the conclusion), but the result demanded an (m−1)-dimensional level and was **false** (centered circle, per the d1084643 header); d1084643 (not listed): narrowing — it fixes the falsity by assuming the core rather than relaxing the dimension requirement |
| t97A02 | stronger | compact T2, locally connected, locally contractible, finite singular H₁ → every map to T² is null; generalizes finite simplicial complexes (still true) | 24ca6edf: correction (bank hypotheses were `opaque` predicates) |
| t97J06 | narrower (part a) | (a) the degree is replaced by ∫∫ det of a hand-entered Jacobian = 0, with no degree notion; (b) actual `¬Homotopic f const` for the concrete map on Circle×Circle, with the lift identity stated | d3852910: correction (bank torus, map, degree and null-homotopy were `def … := by sorry`) |
| t98J03 | faithful | H_*(S⁰) = ℤ², 0; for n>0, H₀ = H_n = ℤ and all others 0, on the metric sphere with singular homology | — (statement unchanged since 886a9386; 25bcef42 predates it) |

## Evidence notes

**t00A04.** The file's own header says "We add the minimal noncontractibility consequence … its identity is not homotopic to a constant map." The theorem is:
```
(ι : X → Y) (r : Y → X), Continuous ι → Continuous r → (∀ x, r (ι x) = x) →
(¬ apm_t00a04_NullHomotopic (fun x : X => x)) → ¬ apm_t00a04_NullHomotopic ι
```
X and Y are arbitrary topological spaces with no manifold structure. The proof is `r ∘ H`. The problem's content is that a closed oriented positive-dimensional manifold is not contractible (top homology / degree), and that is the hypothesis. The positive-dimension gap the header mentions is real: for a point, the claim is false.

**t00J04.** Current conclusion:
```
∃ (f : X → ℝ) (omega : T00J04OneForm X), ContMDiff … ∞ f ∧ (∀ x, omega x = extDerivFun f x) ∧
  omega p = omega_p ∧ t00J04DifferentialIsClosed f
```
`t00J04DifferentialIsClosed` is `extDeriv` of `ofSubsingleton (fderiv (f ∘ chart.symm))` at every chart point, which is a genuine d(df)=0. The bank (4d7b2110) used `opaque apm_t00J04_IsSmoothOneForm / IsClosedOneForm / IsExactOneForm`, which cannot be proved or interpreted. c64226d7 replaced this with `∃ f, ContMDiff f ∧ mfderiv f p = omega_p`. dfc0a31b (the listed repair) added the explicit ω and closedness conjunct, making it closer to (b).

**t01A06.** `t01A06OmegaPullback R r u v := r * (R + r cos v)^2 * sin²u * cos v`. I checked by hand: ω = x dy∧dz − d(yx dz) = −y dx∧dz, whose pullback under the (outward, (u,v)-ordered) parametrization is exactly this. So the value 2π²Rr² is right, but the pullback step is precomputed in the statement, and `t01A06Param` is defined but unused by the theorem. Part (b) uses `IsT01A06ClosedOneForm` (C^∞ plus symmetric derivative) and `IsT01A06LoopOnTorus` (smooth, 2π-periodic, lands in the torus set), which is faithful.

**t01J03.** `apm_t01J03_hasTwiceSpiral`: `c₁ ∘ incl_* = pr₂ ∘ e₁`, so e₁-(1,0) is the meridian, and `e₂(h_*(e₁⁻¹(1,0))) = (1,2)`. The meridian therefore goes to meridian + 2·longitude, giving L(2,1) = RP³. Conclusions: π₁ ≅ ℤ/2, H₀ = ℤ, H₁ = ℤ/2, H₂ = 0, H₃ = ℤ, H_{≥4} = 0. The statement is identical to bank 082028c1.

**t02A03.** `apm_t02a03_Y` is the quotient `Torus ⊕ Circle / (1,1) ~ 1`. The header reads "The two complements are represented by their explicit deformation-retract models." The conclusions are about π₁(T²) and π₁, H_* of T²∨S¹ (ℤ²∗ℤ; ℤ, ℤ³, ℤ, 0), which are the correct answers. D²×S¹∖K and W∖C never appear.

**t91A01.**
```
∀ … (zeros : Finset α) (index : α → ℤ) (genus : ℕ) (p : α),
  (∑ q ∈ zeros, index q) = 2 - 2 * (genus : ℤ) → p ∈ zeros → index p = 3 → ∃ q ∈ zeros, q ≠ p
```
No vector field or surface appears in (b). The header says so explicitly: "records exactly the finite-index conclusion of Poincaré–Hopf together with the classification formula".

**t91A04.** `∃! z : M, T z = z` under `[CompleteSpace M] [Nonempty M]`, `0 ≤ c < 1`. The content is faithful, and uniqueness is extra. The pre-repair file (25bcef42) had no `apm_t91a04` theorem.

**t91A07.** `(E) [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f)`, with `Function.Bijective (fderiv ℝ f x - id)` at fixed points, concluding `∃ U ∈ 𝓝 x, ∀ y ∈ U, f y = y → y = x`. The mathematics is local, but the manifold X is replaced by a vector space and f is required to be globally defined on it.

**t91J02.** `¬Nonempty (Circle × Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`. This is direct.

**t92J02.** `grep` finds no `apm_t92j02` anywhere. The file contains `image_of_compact_isCompact` and `homeomorph_of_compact_to_T2` (with `IsCompact univ`, equivalent to CompactSpace) inside the `ApmCanaries.Frames…` namespace. Both are faithful, but there is no registered theorem to grade.

**t92J07.** Current conclusion: `∃ x, ∀ i : PNat, apm_t92J07_IsSmoothRegularFiber (f i) x ((f i) ⁻¹' {x})`, where that predicate is `s = f ⁻¹' {x} ∧ IsRegularValue f x` (surjective `mfderiv` on the fiber). The bank had `IsRegularValue … ∧ apm_t92J07_IsSmoothSubmanifold …` with `opaque apm_t92J07_IsSmoothSubmanifold`. The repair drops that conjunct, which could never be discharged or interpreted. The M_x → M_i typo repair and the T2/second-countable additions are correct.

**t93A02.** `t93A02H X := {A // A.Nonempty ∧ IsClosed A ∧ IsBounded A}`. It proves that every Hausdorff-Cauchy sequence has L with `hausdorffDist (A n) L → 0`. The glb formula equals `hausdorffDist`, and excluding the empty set is necessary for D to be a metric.

**t94A02.** There is no `apm_t94a02`. `separate_closed_sets`: `∃ f, Continuous f ∧ f '' univ ⊆ Icc 0 1 ∧ f ⁻¹' {0} = A ∧ f ⁻¹' {1} = B`, which is faithful.

**t94J02.** Current: `(∀ τ, τ < σ → ¬@CompactSpace X τ) ∧ (∀ τ, σ < τ → ¬@T2Space X τ)`. In Mathlib, `t₁ ≤ t₂` means t₁ is finer, so this is correct. The 02108503 statement had `σ < τ → ¬Compact` and `τ < σ → ¬T2`. That is false: an indiscrete τ is coarser and compact. The repair commit cb8af566 records the counterexample X=Bool, σ=⊥, τ=⊤ as machine-checked.

**t94J06.** `apm_t94J06_function z = z^4 + 5z^3 + I z^3 + ↑(Real.cos ‖z‖)` and `∃ z, … = 0`. This is literal.

**t95A03.** There is no `apm_t95a03`. `totally_bounded_complete_compact (X) [PseudoMetricSpace X] [CompleteSpace X] (h : TotallyBounded univ) : CompactSpace X` answers "prove", which is correct.

**t95J04.** Part (a): `∀ k < n, ∀ M [T2] [SecondCountable] [Compact] [ChartedSpace (E k) M] [IsManifold … ∞ M] f, ContMDiff … f → μH[n] (range f) = 0 ∧ ¬Surjective f ∧ NullHomotopic f`. Part (b): `SimplyConnectedSpace` for S⁶, S²×S⁴, S³×S³ plus three `¬Nonempty (_ ≃ₜ _)`. The bank's `T95J04CompactSmoothManifold`, `T95J04SmoothMap`, `IsT95J04NullHomotopic` and the rest were all `def … := by sorry`. 9348ebeb's `T95J04SmoothMap` carried `missesPoint_of_dim_lt : k < n → ¬Surjective toFun`, which is the Sard step, supplied as data. e7008638 removed it. The switch from CP³ to S²×S⁴ is a free choice, since the problem says "list three".

**t96J05.** Current hypotheses include `(r) (hr : 0 < r) (hlevel : Nonempty (radialLevel X r))` and `hdata : ∃ charts, … ∀ x : X, ‖x‖^2 = r^2 → Surjective (mfderiv (‖·‖^2) x)`. The conclusion is `∃ r > 0, Nonempty (radialLevel X r) ∧ IsSmoothRadialLevel (m := m) X r`, i.e. some (m−1)-dimensional smooth manifold structure on the level. Finding the regular value is the Sard content, and it is assumed. The problem says only "a non-empty smooth manifold". A centered circle X has X∩S = X, which is a smooth manifold, so the source claim is true. c494d495's demand for an (m−1)-dimensional atlas is what made it false. In the bank, `apm_t96j05_RegularValue ρ c` requires only `∃ U, x ∈ U ∧ MapsTo ρ U (Ioo (c-1) (c+1))` with U not required to be open, so U = {x} satisfies it trivially. The disjunctive hypothesis then hands over the conclusion.

**t97A02.** Current: `[T2Space X] [CompactSpace X] [LocallyConnectedSpace X] (hX : LocallyContractibleSpace X) [Finite (singular H₁ X)]` ⇒ `∃ p, Homotopic f (const p)`. `LocallyContractibleSpace` is Mathlib's classical definition. The bank used `opaque apm_t97A02_IsFiniteSimplicialComplex` and `opaque apm_t97A02_FirstHomologyIsFinite`.

**t97J06.** Current: (i) the lift identity for `t97J06Map` on `Circle × Circle`; (ii) `∫₀¹∫₀¹ det !![2π cos(2πx+4πy), 4π cos(2πx+4πy); 1, 1] = 0`; (iii) `∀ q, ¬ Homotopic t97J06Map (const q)`. The Jacobian entries are correct partials of the lift, but "degree" is not defined; (ii) is a calculus proxy. The bank's `t97J06Torus`, `t97J06Map`, `t97J06Degree` and `IsT97J06NullHomotopic` were `by sorry`. The periodicity typo repair (equivariance modulo ℤ²) is correct.

**t98J03.** `Nonempty (H 0 0 ≅ ℤ×ℤ) ∧ (∀ k>0, IsZero (H 0 k)) ∧ ∀ n>0, H n 0 ≅ ℤ ∧ H n n ≅ ℤ ∧ ∀ k ≠ 0, k ≠ n → IsZero (H n k)`, using singular homology of the metric sphere. This is the complete answer.

# Fidelity grades — list 1

Grader: read-only; nothing built, run or edited in `/home/joe/code/apm-lean`. None of the 21 bundles has a `STATEMENT-REPAIR.md`. Repair classifications come from `git show <bank-sha>:…/Main.lean` and `git show <repair-sha>`. For every REPAIRED problem, the `theorem` header at the repair sha matches HEAD textually, so HEAD's statement is the repaired statement.

| id | grade | one-line reason | repair classification |
|---|---|---|---|
| t00A01 | hypothesis-carries-core | The facts linking M_i to the pieces A, B (each punctured piece is a homology ball and keeps π₁(M_i)) and the S² decomposition are all hypotheses. hM₁, hM₂ are never used. | — |
| t00J03 | vacuous | The integrals are over an explicit half-circle path that the statement never ties to RP¹. The form is identically 1 on that path, so the claim reduces to ∫₀^π 1 dθ = π plus the descent the problem already grants. | — |
| t01A03 | hypothesis-carries-core | (a) assumes the middle circle induces 0 on H₁. (b) assumes π₁(wedge) → π₁(T²) is non-injective. These are exactly the obstructions to be proved. Only (c) (connected ↛ disconnected) is proved from scratch. | — |
| t01J02 | faithful | Bijectivity of the real postcomposition map on `HomotopyGroup.Pi n` for a covering, n ≥ 2. | c6c022bd: correction (the bank's induced map was an `opaque` constant) |
| t02A02 | narrower | A combinatorial surrogate: F is never constructed, V = 3 is only bounded below, and the surface name comes from a hand-written lookup table. The answer (Klein bottle) is correct. | — |
| t03J06 | faithful | Uses the real `extDeriv` (value 3 on the standard frame, not closed, not exact), and the bullet integral is a concrete sum over outward parametrizations. The value 7π checks by Stokes. | c9fe56f6: correction (the bank's integral was a `sorry`-typed placeholder) |
| t91A03 | faithful | Product of compact spaces is compact (`IsCompact univ`). Note: there is no `theorem apm_t91A03`; the theorem is `isCompact_prod` in a canary namespace. | — |
| t91A06 | faithful | Compact T2 space: a countable intersection of dense open sets is dense. | — |
| t91J01 | faithful | No continuous surjection, and a continuous injection exists, from `cantorSet` to the irrationals in (0,1). | — |
| t92J01 | faithful | `[Nonempty A]` is only needed because Mathlib's `IsConnected` requires nonemptiness. | — |
| t92J04 | faithful | Lebesgue number lemma. `[Nonempty X]` only rules out the degenerate empty space. | — |
| t93A01 | faithful | Both parts stated directly, with second countability. | — |
| t93J02 | faithful | Hypotheses `hclosed` and `hne` are redundant: they follow from T2 + compact and from `IsConnected`. | — |
| t94J01 | faithful | Preconnectedness of univ ↔ ladder connected. Note: there is no `theorem apm_t94J01`; the theorem is `connected_iff_ladderConnected` in a canary namespace. | — |
| t94J05 | faithful | A `ContMDiff` ∞ map T² → S³ is homotopic to the constant map at (0,0,0,1). | ca540c23: correction (the bank's smoothness was an `opaque` predicate; see note) |
| t95A02 | faithful | Perfect map onto a compact space has a compact domain. | — |
| t95J03 | hypothesis-carries-core | `hnecessary` + `hrealize` force the cover relation to equal hand-written constraints, and `hrealize` is false for genuine covers (e.g. S², k = 2). What is left is Euler-characteristic arithmetic. | f7d26649: correction (the bank type and predicate were `sorry`); 63cc765d: neutral (logically equivalent to f7d26649) |
| t96J04 | faithful | There is no continuous surjection ℝ×ℚ → ℝ∖ℚ. | — |
| t96J08 | faithful | Not closed, not exact (real `fderiv`), and a parametrized hemisphere integral of 5π/3, which checks by Stokes. dω is a hand-coded formula, and it is correct. | — |
| t97J03 | faithful | No continuous extension over D×S¹ of (z,w) ↦ (z,w³). D¹ is read as the complex unit disk. | — |
| t98A05 | faithful | dα, dβ = 3γ, dγ = 0, α∧β = 0, ∫_Γ dα = 1, dα′ = 0 and α′ not exact, all as concrete encodings. Γ is read as the 2-simplex face. | cf6cbdd0: correction (bank wedge, integral, circle d and exactness were `opaque`) |

## Evidence notes

**t00A01.** The theorem quantifies over arbitrary A, B with
`(hA : apm_t00A01_isHomologyBall A) (hB : …)`,
`(hπA : Nonempty (FundamentalGroup A a ≃* FundamentalGroup M₁ m₁))`,
and `(hcover : apm_t00A01_hasStandardCover (apm_t00A01_connectedSum iA iB) A B)`. `hasStandardCover` supplies open U, V with U ≃ₕ A, V ≃ₕ B and U∩V ≃ₕ S².

- The conclusion is `FundamentalGroup X x ≃* Monoid.Coprod (π₁ M₁) (π₁ M₂) ∧ isHomology3Sphere X`.
- Van Kampen and Mayer–Vietoris are really proved (bridges at l.201 and l.245).
- But "M_i minus a 3-simplex is a homology ball with the same π₁" is part of the problem's content, and here it is assumed. `hM₁` and `hM₂` are not passed to either bridge, so M_i enter only through `hπA`/`hπB`.
- The quotient cover is also assumed rather than derived from the gluing.

**t00J03.**
```lean
(∫ θ in (0 : ℝ)..Real.pi, eta (apm_t00j03_tangentClass θ)) = Real.pi ∧
(∫ θ in Real.pi..(0 : ℝ), eta (apm_t00j03_tangentClass θ)) = -Real.pi
```
- `tangentClass θ` is the class of `(cos θ, sin θ), (−sin θ, cos θ)`, where the form evaluates to 1 (`apm_t00j03_angleFormValue_circle`).
- The only RP¹ content, `Function.Surjective apm_t00j03_projectivize`, is a separate conjunct unrelated to the path.
- Nothing states that θ ∈ [0,π) parametrizes RP¹ once, which is where the problem's orientation discussion happens. The ±π values are correct.

**t01A03.**
```lean
Topology.IsEmbedding middle → apm_t01a03_H1map middle = 0 →
Topology.IsEmbedding wedgeInTorus →
¬Function.Injective (FundamentalGroup.map wedgeInTorus apm_t01a03_wedgeBase) → …
```
- For (a), the proof is "zero H₁ map + H₁(S¹) ≠ 0 ⇒ no retraction". For (b), it is "non-injective π₁ map ⇒ no retraction". The hypotheses hand over exactly the fact that makes each part non-trivial.
- The genus-two hypothesis `apm_t01a03_hasGenusTwo S` is unused.
- The answers (no, no, no) are correct.

**t01J02.**
- Current statement: `Function.Bijective (apm_t01j02_inducedMap n ⟨p, hp.continuous⟩ xtilde₀ x₀ hbase)`, where `inducedMap` is `Quotient.map` of postcomposition, transported along `hbase`. The problem already grants that the map is a homomorphism, so bijective = isomorphism.
- Bank (b8f57240): `opaque apm_t01j02_inducedMap … : HomotopyGroup.Pi n Xtilde xtilde₀ → HomotopyGroup.Pi n X x₀`. It is an unconstrained constant, so the bank claim did not concern p_* and could not be proved.
- The repair is a correction. The theorem header is otherwise unchanged apart from passing the bundled continuous map.

**t02A02.**
- The answer, Klein bottle (χ = 3 − 4 + 1 = 0, nonorientable), is correct. I checked the vertex classes independently: {0,1,2,6}, {3,5,7}, {4}.
- The statement, however:
  - never builds the glued space;
  - `apm_t02a02_validVertexQuotient ∧ Function.Surjective apm_t02a02_vertexClass` only shows the true vertex classes number at least 3. A consistent labeling can merge classes, so 3 is a lower bound;
  - uses the literal `Nat.card (Fin 3)` in the χ conjunct;
  - has `apm_t02a02_classify false 0 = .kleinBottle`, which holds by `rfl` from a hand-defined table whose arguments are literals, not derived from the earlier conjuncts.

**t03J06.**
- The current statement keeps the real `extDeriv omega x (single frame) = 3`, `extDeriv omega ≠ 0` and `¬∃ eta … extDeriv eta = omega`.
- `apm_t03J06_bulletIntegral` = cylinder integral with tangents (−sin θ, cos θ, 0), (0,0,1) (outward normal) + hemisphere graph integral with tangents (1,0,−x/s), (0,1,−y/s) (upward normal). This matches "dx∧dy positive at (0,0,2)".
- The value checks: dω = 3 dV, volume 8π/3, and the bottom disk contributes π, so the integral is 8π − π = 7π.
- Bank (ca408fed): `def apm_t03J06_bulletIntegral (_surface) (_omega) : ℝ := by sorry`. The fifth conjunct was about an unspecified real number.
- Repair c9fe56f6 is a correction. The other four conjuncts are unchanged.

**t91A03.** `theorem isCompact_prod (hX : IsCompact (univ : Set X)) (hY : IsCompact (univ : Set Y)) : IsCompact (univ : Set (X × Y))`. This is faithful, but no `apm_t91A03` theorem exists in Main.lean.

**t91A06.** `Dense (⋂ i, U i)` for `U : ℕ → Set X` that are open and dense, with `[CompactSpace X] [T2Space X]`.

**t91J01.** `(¬∃ f : C(cantorSet, {x // Irrational x ∧ 0 < x ∧ x < 1}), Surjective f) ∧ ∃ f, Injective f`. Both answers are correct.

**t92J01.** `[Nonempty A]` with `hConn : ∀ a, IsConnected (C a)`, `hx : ∀ a, x ∈ C a` ⊢ `IsConnected (⋃ a, C a)`. The nonempty index only compensates for Mathlib's nonempty-connected convention.

**t92J04.** The conclusion is `∃ ε > 0, ∀ C, Metric.diam C < ε → ∃ V ∈ U, C ⊆ V`, for U an open cover of a compact metric X with `[Nonempty X]`.

**t93A01.** The conclusion is `(∃ C : ℕ → Set X, (∀ n, IsClosed (C n)) ∧ U = ⋃ n, C n) ∧ (∃ f : X → Icc 0 1, Continuous f ∧ (∀ x ∈ U, 0 < f x) ∧ ∀ x ∉ U, f x = 0)`.

**t93J02.** The conclusion is `IsCompact (⋂ n, C n) ∧ IsConnected (⋂ n, C n)`. The extra hypotheses `hclosed` and `hne` follow from the others, so they do not narrow the statement.

**t94J01.** `connected_iff_ladderConnected : IsPreconnected (univ : Set X) ↔ LadderConnectedSpace X`. `LadderChain` encodes a finite sequence of cover members with consecutive nonempty overlaps, p in the first and q in the last. `IsPreconnected` matches the separation definition and so covers the empty space. There is no `apm_t94J01` theorem.

**t94J05.**
- Current hypothesis: `(hf : ContMDiff ((𝓡 1).prod (𝓡 1)) (𝓡 3) (⊤ : ℕ∞) f)`.
- Conclusion: `ContinuousMap.Homotopic f (ContinuousMap.const _ apm_t94J05_northPole)`.
- Bank (f17dac94): `opaque apm_t94J05_IsSmooth (f : C(Torus, S3)) : Prop`.
- Because the opaque predicate has no eliminator, the bank's provable content was the claim for all continuous maps T² → S³. That claim is true, but the problem does not ask for it, and the opaque predicate does not express smoothness.
- I classify the repair as a correction. Strictly, it also says less than the bank's effective all-continuous-maps content, but it now matches problem.md.

**t95A02.** `apm_t95A02_IsPerfectMap f := Continuous f ∧ IsClosedMap f ∧ Surjective f ∧ ∀ y, IsCompact {x | f x = y}`, with `[CompactSpace Y]` ⊢ `IsCompact (univ : Set X)`.

**t95J03.**
- Current hypotheses: `(hnecessary : ∀ k F P, HasConnectedKFoldCover k F P → T95J03CoverConstraints k F P)` and `(hrealize : ∀ k F P, T95J03CoverConstraints k F P → HasConnectedKFoldCover k F P)`. Together they make the parameter extensionally equal to `CoverConstraints`: χ multiplies by k, with an orientability rule.
- `hrealize` fails for the genuine cover relation: S² with k = 2 satisfies the constraints with profile (orientable, χ = 4), but no such connected cover exists. So the theorem applies only to relations equal to the constraint table, and the problem's substance ("which surfaces actually share a cover") lives in the hypotheses.
- The answer `if Even k then {torus, Klein} else {Klein}` is correct.
- Bank (52c43390): `def T95J03ClosedSurface : Type := by sorry`, with the torus, Klein bottle and cover predicate all `sorry`. That is not a meaningful statement, so f7d26649 is a correction. f7d26649 hard-coded the constraints as the definition of admitting a cover.
- 63cc765d turns that definition into a parameter plus an iff pair of hypotheses. Given the hypotheses, the theorem is logically equivalent to the f7d26649 version, so it is neutral: it relabels where the core sits without changing it.

**t96J04.** `¬ ∃ f : ℝ × ℚ → {x : ℝ // Irrational x}, Continuous f ∧ Function.Surjective f`.

**t96J08.**
- Conclusion: `¬apm_t96j08_IsClosed ∧ ¬apm_t96j08_IsExact ∧ apm_t96j08_hemisphereIntegral = 5 * Real.pi / 3`.
- `IsClosed` is stated through the hand-written `apm_t96j08_domega = det(u,v,w)`. That is the correct dω, since the coefficients are 1 − 1 + 1 = 1, but the statement does not link it to `omega`.
- `IsExact` uses genuine `fderiv` of a smooth 1-form.
- The hemisphere parametrization has tangents (1,0,−x/s), (0,1,−y/s), positive at (0,0,2).
- The value checks: half-ball volume 2π/3, and the bottom disk (downward) contributes −π, so the integral is 5π/3.

**t97J03.** `¬ ∃ F : Disk × Circle → Circle × Circle, Continuous F ∧ ∀ q, F (boundaryInclusion q) = boundaryMap q`, with `boundaryMap (z,w) = (z, w^3)`. D¹ is read as the complex unit disk, which is what "solid torus in ℂ²" needs.

**t98A05.**
- Current conjuncts:
  - `extDeriv alpha x v = 2 * (v 0 0 * v 1 1 - v 0 1 * v 1 0)`, `extDeriv beta = 3 • gamma` and `extDeriv gamma = 0` (real `extDeriv`);
  - `apm_t98a05_wedgeEval alpha beta x v = 0` (explicit shuffle formula);
  - `apm_t98a05_orientedSimplexIntegral (extDeriv alpha) = 1` (parametrization with tangents (1,0,−1), (0,1,−1), normal (1,1,1));
  - `apm_t98a05_isCircleClosed alpha` (ambient dα vanishes on circle-tangent pairs);
  - `¬∃ f, apm_t98a05_IsDifferential f alpha'` (derivative along every differentiable curve). This quantifies over a class of f at least as large as the smooth ones, so the nonexistence claim is at least as strong as the problem's.
- All values check.
- Interpretive point: Γ as literally worded is the solid tetrahedron, but a 2-form needs a surface, so reading it as the triangular face is a defensible encoding choice.
- Bank (87af3cf9): `opaque apm_t98a05_wedge`, `opaque apm_t98a05_orientedIntegral`, `opaque apm_t98a05_circleExtDeriv`, `opaque apm_t98a05_IsDifferential`. Four of the seven conjuncts concerned unconstrained constants.
- Repair cf6cbdd0 is a correction. The three `extDeriv` conjuncts and the simplex/orientation reading are unchanged.

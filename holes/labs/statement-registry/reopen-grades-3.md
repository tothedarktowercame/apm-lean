# Reopen grades 3 — fidelity of rewritten open statements

Repo: /home/joe/code/apm-lean. Graded the current `theorem apm_<id>` only
(`apm_<id>_previous_encoding` ignored). Read-only; nothing built. Mathlib
checked in `.lake/packages/mathlib`: in `ContDiff` scope `ω` is
`(⊤ : WithTop ℕ∞)` (analytic) and `∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)` (smooth)
(`Analysis/Calculus/ContDiff/FTaylorSeries.lean:112,114`).

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00J03 | narrower | `apm_t00j03` | Descent is stated, but "∫ over RP¹" is replaced by an integral over a chosen half-circle whose once-covering of RP¹ is never stated; only endpoint equality is asserted, which a full circle (answer 2π) would also satisfy | no |
| t01A07 | faithful | `apm_t01a07` | (a) regular-cone gradient criterion (sufficient for submanifold); (b) signed two-point chart sum = 0, which is the correct integer answer since H₂(RP³;ℤ)=0; sign rule is sound because deg 4 is even. Stale docstring still says "mod-2" | no |
| t02A03 | faithful | `apm_t02a03` | Actual complements X and W∖C are stated homotopy-equivalent to T² and T²∨S¹, with π₁ and all Hₙ of the models; concrete W is an encoding choice | claimed defect is not real (underspecification up to isotopy, not an error); the concrete model is not a departure and narrows nothing |
| t91A07 | faithful | `apm_t91a07` | General boundaryless manifold, nondegeneracy as bijectivity of d(chart∘f∘chart⁻¹) − id at a fixed point, isolation conclusion | no |
| t96J05 | narrower | `apm_t96j05` | Conclusion only says X∩S_r admits *some* smooth atlas of *some* dimension (no link to the ambient ℝⁿ, i.e. not a submanifold); hypothesis uses `⊤` = ω, restricting X to real-analytic submanifolds | no (prelim is correct; the centered-circle case satisfies it with X∩S = X) |
| t97J08 | faithful | `apm_t97j08` | Explicit β, β = φ*α̂ (with hand-written dφ that is correct), coordinate closedness, and winding number (periodic homotopy to e^{int}) equals ∫₀^{2π} f*β | no |

## Evidence notes

### t00J03 — narrower
The statement:
```lean
theorem apm_t00j03 :
    apm_t00j03_projectiveLoop 0 = apm_t00j03_projectiveLoop Real.pi ∧
    ∃ eta : apm_t00j03_ProjectiveTangent → ℝ,
      (∀ (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane),
        eta (Quotient.mk _ (x, v)) = apm_t00j03_angleFormValue x v) ∧
      apm_t00j03_projectiveLoopIntegral eta = Real.pi ∧
      (∫ θ in Real.pi..(0 : ℝ), eta (apm_t00j03_tangentClass θ)) = -Real.pi
```
with `projectiveLoopIntegral eta := ∫ θ in 0..π, eta (tangentClass θ)`.
- Descent part is sound: `ProjectiveTangent` is (x,v) modulo
  (x,v) ~ (λx, λv + a·x), which is T RP¹ (T_x ℝ²/ℝx, transported by dm_λ);
  existence of `eta` with the displayed pullback equation is exactly
  invariance of the angle form. Good.
- Integral part: the problem asks for ∫_{RP¹} ω. The Lean integral is along
  θ ↦ [cos θ, sin θ] on [0,π]. Nothing in the statement says this loop is a
  bijection [0,π) → RP¹ (degree ±1). The only geometric clause is
  `projectiveLoop 0 = projectiveLoop π`, i.e. that the loop closes. The same
  clause holds for [0,2π], which gives 2π — the standard wrong answer the
  problem is testing. The choice of fundamental domain, which is what decides
  π versus 2π, is supplied by the definition `apm_t00j03_projectiveLoopIntegral`,
  not proved. Once `eta` is built, the conclusion is `∫₀^π 1 = π`.
- Orientation clause is interval reversal (`∫ π..0 = -π`), true for any
  integrand with ∫₀^π = π; it records "reversing orientation flips sign" but
  no orientation of RP¹ is defined.
- Missing conjunct needed for fidelity, e.g.
  `Set.BijOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) Set.univ`
  (and ideally a local-diffeomorphism/immersion property of the loop).
- Module docstring's "Statement repairs" (reading final ℝ² as ℝ²∖{0}) is
  reasonable.

### t01A07 — faithful (with caveats)
```lean
theorem apm_t01a07 :
    apm_t01a07_IsSmoothProjectiveHypersurface ∧
      apm_t01a07_pointPlus ≠ apm_t01a07_pointMinus ∧
      apm_t01a07_surface ∩ apm_t01a07_line =
        {apm_t01a07_pointPlus, apm_t01a07_pointMinus} ∧
      apm_t01a07_orientedIntersectionNumber = 0
```
- (a) `IsSmoothProjectiveHypersurface := ∀ v ≠ 0, quartic v = 0 → fderiv ℝ quartic v ≠ 0`.
  This does not assert a submanifold structure; it asserts the regular-cone
  criterion from which "S is a smooth submanifold of RP³" follows by the regular
  value theorem (on S³, then pass to the ±1 quotient). That is the standard
  proof content, so I accept it as an encoding choice. The file's claim that
  the criterion is "equivalent" is wrong in general (X² = 0 cuts out a smooth
  hyperplane with vanishing gradient); it is only sufficient. Here it is
  sufficient, so stating it is not a narrowing.
- (b) `orientedIntersectionNumber := localIntersectionSign 1 + localIntersectionSign (-1)`,
  `localIntersectionSign y := if 0 < deriv lineQuartic y then 1 else -1`,
  `lineQuartic y = quartic ![1, y, 0, 0] = 1 − y⁴`. Signs: −1 at y=1, +1 at
  y=−1, sum 0. I checked that the sign rule is sound: deg 4 is even, so the
  sign of the quartic is well defined on RP³ and co-orients S globally; the
  sign of d/dy of the quartic along any lift at a zero does not depend on the
  lift (λ⁴ > 0); ℓ is oriented by the y-chart, which covers ℓ minus one point
  and contains both intersection points. So the sum is I(S,ℓ) up to a global
  sign, and 0 is correct (H₂(RP³;ℤ) = 0, so any closed oriented S is
  null-homologous). Caveats: the sum hard-codes y = ±1 rather than summing
  over `surface ∩ line` (clause 3 pins the set; `pointPlus = [lineChart 1]`
  holds by inspection, but no clause says so); the non-transverse branch
  returns −1 silently (not triggered). The sign-rule argument above is not
  in the file.
- Stale docs: the module docstring still says part (b) "is stated as the
  orientation-free mod-2 intersection number. This is a declared weakening."
  The current theorem is integer-valued. Should be fixed so the registry
  record is not misleading.

### t02A03 — faithful; PRELIM-DEFECT claim not a real defect
```lean
theorem apm_t02a03 :
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_X apm_t02a03_Torus) ∧
    Nonempty (ContinuousMap.HomotopyEquiv apm_t02a03_geometricY apm_t02a03_Y) ∧
    Nonempty (FundamentalGroup apm_t02a03_Torus (1, 1) ≃* Multiplicative (ℤ × ℤ)) ∧
    Nonempty (FundamentalGroup apm_t02a03_Y apm_t02a03_ybase ≃*
        Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)) ∧
    ... H₀ ≅ ℤ, H₁ ≅ Fin 3 → ℤ, H₂ ≅ ℤ, ∀ n ≥ 3, IsZero Hₙ   -- of apm_t02a03_Y
```
- `apm_t02a03_X := {p : closedBall (0:ℂ) 1 × Circle // p.1.1 ≠ 0}` is the
  actual D²×S¹ ∖ ({0}×S¹). `geometricY := {p ∈ ℝ³ // p ∈ W ∧ p ∉ C}` is an
  actual complement in ℝ³. The π₁/Hₙ claims are about the models T² and
  T²∨S¹ (the wedge `Y` is a genuine quotient space), and the homotopy
  equivalences to the actual spaces are conclusions, not hypotheses. π₁ and
  singular homology are homotopy invariant, so this states the requested
  computations; the reader has to compose one standard step, which I accept.
- Model check: spine = two unit circles centred at (±1,0,0), tangent at the
  origin; W = closed 1/4-neighbourhood; C = left circle. I checked the
  distance-to-spine function for generalised critical points in (0, 1/4]: the
  hole centres (±1,0,0) are at distance 1; on the medial axis near the origin
  (points (0,y,0)) the two nearest-point directions do not cancel; points
  (0,0,z) have the unique nearest point 0. So W retracts onto the figure-eight
  and is a genus-two handlebody; the answers T², T²∨S¹, ℤ², ℤ²∗ℤ, (ℤ, ℤ³, ℤ, 0)
  are correct. C passes through the wedge point (it touches the right
  circle at 0); this does not matter, because C can be isotoped inside int W
  off the right circle, but the file does not mention it.
- PRELIM-DEFECT.md: it claims that "standardly embedded genus two surface" and
  "in the same way" do not specify a subset of ℝ³. That is true but is not
  a defect: the prelim fixes W and C up to ambient isotopy, which fixes all
  requested invariants. Picking a concrete model is an ordinary encoding
  choice. It narrows nothing, so it is the smallest possible departure (in
  effect none). Stale docs: the module docstring says "Statement repairs:
  None" and "The two complements are represented by their explicit
  deformation-retract models", which describes the superseded encoding.

### t91A07 — faithful
```lean
theorem apm_t91a07 (E) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X) [TopologicalSpace X] [ChartedSpace E X] [IsManifold (modelWithCornersSelf ℝ E) ∞ X]
    (f : X → X) (hf : ContMDiff 𝓘 𝓘 ∞ f)
    (hnondegenerate : ∀ x, f x = x → Function.Bijective
        (fderiv ℝ ((extChartAt 𝓘 x) ∘ f ∘ (extChartAt 𝓘 x).symm) (extChartAt 𝓘 x x)
          - ContinuousLinearMap.id ℝ E)) :
    ∀ x, f x = x → ∃ U ∈ 𝓝 x, ∀ y ∈ U, f y = y → y = x
```
- At a fixed point, f(x) = x, so the composite agrees with the true coordinate
  expression on a neighbourhood of φ(x) (chart target is open for
  `modelWithCornersSelf`), and its `fderiv` there is df_x in coordinates.
  In finite dimension, "df_x − id bijective" ⇔ "+1 is not an eigenvalue".
  The hypothesis is placed on df_x, as it should be.
- Conclusion is exactly isolation. General manifold (no boundary, no
  Hausdorff assumption needed); smooth = `∞` (not ω). Nothing dropped.

### t96J05 — narrower
```lean
theorem apm_t96j05 (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) (X : Set (apm_t96j05_E n))
    (hXne : X.Nonempty) (hXconn : IsConnected (Set.univ : Set X))
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X) :
    ∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_HasSmoothManifoldStructure (apm_t96j05_radialLevel X r)
```
- Conclusion weakened: `HasSmoothManifoldStructure Y := ∃ k, ∃ charts :
  ChartedSpace (E k) Y, IsManifold (I k) ∞ Y`. This says only that
  X ∩ S_r (with subspace topology) admits some abstract smooth atlas of some
  dimension, with no relation to the smooth structure of ℝⁿ or of X. The
  problem's "X ∩ S is a smooth manifold", for a subset of ℝⁿ, means a
  smooth submanifold. The statement cannot tell a smooth submanifold from
  any subset that happens to be smoothable (e.g. any topological 1-manifold,
  or any discrete set). Fidelity would need the conclusion to be the
  submanifold predicate itself, e.g. `IsEmbeddedSmoothSubmanifold (m := k)
  {x | x ∈ X ∧ ‖x‖ = r}` for some k (with smooth `∞`, and ideally an
  immersion condition). "Some k" is right, since the centered circle
  (X ⊂ S_R) needs k = m.
- Hypothesis narrowed: `apm_t96j05_IsEmbeddedSmoothSubmanifold` uses
  `IsManifold (apm_t96j05_I m) ⊤ X` and `ContMDiff … ⊤ (fun x : X ↦ x.1)`.
  In this Mathlib `⊤ : WithTop ℕ∞` is `ω`, so the hypothesis requires a
  real-analytic atlas with analytic inclusion. A smooth, non-analytic
  submanifold (e.g. the graph of a flat bump function) admits no such
  structure, so the theorem only covers real-analytic X. `∞` should be used.
- The hypothesis also does not require the inclusion to be an immersion
  (a topologically embedded cusp satisfies it). That widens the hypothesis
  and so strengthens the statement, and it stays true (Sard for ‖·‖² on X,
  or X itself when ‖·‖ is constant), but it means "embedded smooth
  submanifold" is only approximated.
- Not vacuous: hypotheses are satisfiable and the weak conclusion is not
  immediate for general X.
- No PRELIM-DEFECT. The file's "Statement repairs" says the unconditional
  claim is false because of the centered circle. That applies only to the
  superseded (m−1)-dimensional conclusion. The prelim does not demand
  codimension one, and for the circle X ∩ S = X is a smooth manifold. The
  docstring also describes "an explicit positive attained regular value"
  hypothesis that the current theorem does not have (stale).

### t97J08 — faithful
```lean
theorem apm_t97j08 :
    (∀ z : ℂ, z ≠ 0 → ‖t97J08Phi z‖ = 1) ∧
    (∀ z v : ℂ, z ≠ 0 → t97J08Beta z v = t97J08PhiPullbackAlphaHat z v) ∧
    IsT97J08ClosedOneFormOnPuncturedPlane t97J08Beta ∧
    ∀ f : ℝ → ℂ, IsT97J08SmoothPuncturedLoop f →
      ∃! n : ℤ, IsT97J08WindingNumber f n ∧ (n : ℝ) = t97J08BetaIntegral f
```
- (a) Explicit β = (x dy − y dx)/(2π(x²+y²)) is stated to equal
  α(φ z)(Dφ_z v). `t97J08DPhi z v = v/‖z‖ − z·((z·v)/‖z‖³)` is the correct
  differential of z/|z|, but it is hand-written rather than
  `fderiv ℝ t97J08Phi z v`. The clause is true as stated, but nothing in
  the statement ties `DPhi` to the derivative. Minor. Closedness predicate:
  ∂Q/∂x = ∂P/∂y with P = β(·,1), Q = β(·,i). Correct.
- (b) Maps S¹ → ℂ∖0 are 2π-periodic smooth f; ∫_{S¹} f*β is
  `∫ t in 0..2π, β (f t) (deriv f t)`. Here the parametrisation is part of
  the encoding of S¹ as ℝ/2πℤ, and one period covers S¹ exactly once with
  standard orientation, so this is acceptable (unlike t00J03). Degree =
  free homotopy class of the normalized loop through periodic unit loops to
  e^{int}, which is the right notion.
- Caveat: `∃! n, W n ∧ n = ∫` — the uniqueness half is trivial because
  `n = ∫` already fixes n. So the statement says *some* degree witness equals
  the integral. It does not say every one does. Since W is in fact unique (the prelim
  "recall" presupposes it), this is equivalent, but `(∃ n, W n) ∧ ∀ n, W n →
  n = ∫` would say it directly.

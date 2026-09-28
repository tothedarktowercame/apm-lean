# Reopen-2 grades 3: fidelity of second-pass rewrites

Repo: /home/joe/code/apm-lean. I graded the current `theorem apm_<id>` only
(`apm_<id>_previous_encoding` ignored), at commits a1043bf8 (t00A04), 1ee9fc4f
(t00J03) and 77016b2f (t96J05). The working tree is clean for all three
problem dirs. Read-only: nothing built, edited or committed. Smoothness notation was
checked in `.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:112,114`:
`ω = (⊤ : WithTop ℕ∞)`, `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`. All three files
`open scoped ContDiff`, so `∞` in them means C^∞.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00A04 | narrower (accepted under PRELIM-DEFECT); also drops orientation, which strengthens and stays true | `apm_t00a04` | C^∞ now (`∞`), path-connectedness removed; adds `[Nonempty X]` + `0 < finrank E`. This is not quite the minimal fix: a 0-dim X with ≥2 points satisfies the prelim claim but is excluded. `[Nontrivial X]` alone would be exact | yes. The defect is real (one-point X; empty X), but PRELIM-DEFECT.md's "minimal correction" claim overstates things by the 0-dim ≥2-point case |
| t00J03 | faithful | `apm_t00j03` | Now states the loop is continuous, closes, and is injective on [0,π) and surjective onto RP¹. So ∫₀^π is the integral over RP¹ covered exactly once, and the 2π reading is ruled out by InjOn. Minor: the velocity field is hand-written, not stated to be the derivative | no |
| t96J05 | faithful (caveat: no immersion condition) | `apm_t96j05` | Hypothesis now C^∞. Conclusion: the actual subset X∩S_r (subspace topology) carries a C^∞ atlas of some dim k ≤ m with smooth inclusion into ℝⁿ, the same notion as the hypothesis on X. Both sides still omit an immersion condition | no |

## Evidence notes

### t00A04: narrower, accepted under a real PRELIM-DEFECT (the fix is slightly more than minimal)
```lean
theorem apm_t00a04 :
    ∀ (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
      [FiniteDimensional ℝ F] (I : ModelWithCorners ℝ E E)
      (J : ModelWithCorners ℝ F F)
      (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [CompactSpace X] [Nonempty X]
      [T2Space Y] [CompactSpace Y]
      [ChartedSpace E X] [IsManifold I ∞ X]
      [ChartedSpace F Y] [IsManifold J ∞ Y],
      0 < Module.finrank ℝ E →
      ∀ (ι : C(X, Y)) (r : C(Y, X)),
      ContMDiff I J ∞ ι → ContMDiff J I ∞ r →
      (∀ x, r (ι x) = x) → ¬ apm_t00a04_NullHomotopic ι
```
- (c) Smoothness: `IsManifold I ∞`, `IsManifold J ∞` and `ContMDiff … ∞` are C^∞
  (this fixes the previous `⊤` = ω). `PathConnectedSpace X` is gone.
- (a) Hypotheses, object by object:
  - X and Y are compact Hausdorff manifolds. Second countability follows from
    compact + locally Euclidean.
  - `I, J : ModelWithCorners ℝ E E` are arbitrary rather than `𝓘(ℝ,E)`.
    Since `I` is a homeomorphism E → range I, invariance of domain makes the
    range open, so there is no boundary: "without boundary" is respected.
    Allowing a non-standard `I` is a harmless generalisation.
  - "X ⊂ Y submanifold" is encoded as a smooth `ι` with smooth left inverse
    `r`. The equation `r ∘ ι = id` makes dι injective, and X is compact, so
    ι is an embedding. This is therefore equivalent to the prelim's X ⊂ Y
    with f|_X = id.
  - `apm_t00a04_NullHomotopic` is a continuous homotopy on X × ℝ ending at a
    constant, which is equivalent to one on [0,1] by clamping.
- Orientation is dropped for both X and Y. This strengthens the statement,
  which stays true: use the mod-2 fundamental class of a nonempty closed
  n-manifold (n > 0), which survives ι_* because ι has a retraction.
- (b) Trivial cases:
  - One-point X is excluded, since a nonempty open subset of E with finrank
    E > 0 is not a point.
  - Empty X is excluded by `[Nonempty X]`.
  - A constant ι is impossible: X is nontrivial and r ∘ ι = id.
  - A discontinuous ι is excluded by `C(X, Y)`.
  - A 0-dimensional Y forces a finite X, which contradicts positive dimension.
  None of these makes the statement vacuous or false.
- (d) PRELIM-DEFECT.md:
  - The defect is real. With X = {pt} ⊂ Y (a closed oriented 0-manifold) and
    f constant, the inclusion is constant, so the prelim claim is false.
    Empty X with nonempty Y also fails under the Lean definition.
  - The added hypotheses are almost, but not exactly, minimal. A 0-dim X with
    k ≥ 2 points satisfies the prelim claim. If ι ≃ const, all of ι(X) lies in
    one path component P of Y. Then f(P) is connected in discrete X and
    contains X, so X is a single point.
  - So the exact correction is "X has at least two points" (`[Nontrivial X]`
    in place of `[Nonempty X]` + `0 < finrank E`), and it needs no dimension
    hypothesis.
  - PRELIM-DEFECT.md says "the minimal correction is that X is nonempty and has
    positive dimension". That drops the 0-dim ≥2-point case. The case is
    marginal and clearly not what the problem intends, but the word
    "minimal" is inaccurate.
- Stale doc: the module docstring's "Statement repairs" still says "We add …
  its identity is not homotopic to a constant map". That describes the
  superseded hypothesis, not the current theorem.

### t00J03: faithful
```lean
theorem apm_t00j03 :
    Continuous apm_t00j03_projectiveLoop ∧
    Set.SurjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) Set.univ ∧
    Set.InjOn apm_t00j03_projectiveLoop (Set.Ico 0 Real.pi) ∧
    apm_t00j03_projectiveLoop 0 = apm_t00j03_projectiveLoop Real.pi ∧
    ∃ eta : apm_t00j03_ProjectiveTangent → ℝ,
      (∀ (x : apm_t00j03_PuncturedPlane) (v : apm_t00j03_Plane),
        eta (Quotient.mk _ (x, v)) = apm_t00j03_angleFormValue x v) ∧
      apm_t00j03_projectiveLoopIntegral eta = Real.pi ∧
      (∫ θ in Real.pi..(0 : ℝ), eta (apm_t00j03_tangentClass θ)) = -Real.pi
```
- The earlier finding is addressed directly. The loop θ ↦ [cos θ, sin θ] is
  continuous into RP¹ (quotient topology), closes, and is a bijection
  [0,π) → RP¹. A continuous closed loop that is bijective on a fundamental
  interval has degree ±1. So `∫₀^π eta(tangentClass θ)` is ∫_{RP¹} ω in the
  orientation that the loop induces.
- I constructed the bad case: the full circle θ ∈ [0,2π) (answer 2π), which
  corresponds to a double-speed loop on [0,π). Both fail `InjOn` (θ and θ+π
  give the same line), so the clause catches the standard wrong answer.
- Descent: `ProjectiveTangent` = (x,v) modulo (λx, λv + a·x), which is T RP¹.
  The pullback equation determines `eta` uniquely because `Quotient.mk` is
  surjective. That is the descent claim. This part is unchanged from the
  previous grading and still sound.
- Orientation: the negative case is the reversed interval, and the orientation
  of RP¹ is the one the loop induces. That is an acceptable reading of
  "discuss orientation".
- (b) Nothing here is vacuous: every object is concrete, and eta is forced.
- Minor caveat: `circleVelocity θ = (-sin θ, cos θ)` is hand-written. No
  clause says it is `deriv circlePoint θ`, which it is by inspection. This is
  the same class of caveat as t97J08's `DPhi`.

### t96J05: faithful, with a caveat (the embedded-submanifold notion has no immersion condition)
```lean
theorem apm_t96j05 (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) (X : Set (apm_t96j05_E n))
    (hXne : X.Nonempty) (hXconn : IsConnected (Set.univ : Set X))
    (hX : apm_t96j05_IsEmbeddedSmoothSubmanifold (m := m) X) :
    ∃ r : ℝ, 0 < r ∧ Nonempty (apm_t96j05_radialLevel X r) ∧
      apm_t96j05_IsEmbeddedSmoothRadialLevel (m := m) X r
```
where the hypothesis is `∃ charts : ChartedSpace (E m) X, IsManifold (I m) ∞ X ∧
ContMDiff (I m) (I n) ∞ (↑)`. The conclusion is `∃ k ≤ m, ∃ charts on
{x : X // ‖x.1‖ = r}, IsManifold (I k) ∞ ∧ ContMDiff (I k) (I n) ∞ (fun x ↦ x.1.1)`.
- (c) Both predicates use `∞` (C^∞), so the analytic `⊤` is gone.
- The conclusion is now about the actual set X ∩ S_r with the subspace
  topology from ℝⁿ (a subtype of a subtype), with smooth inclusion into ℝⁿ.
  This is the same notion as the hypothesis on X, which is what the earlier
  finding asked for.
- The dimension k is existential with k ≤ m. That is correct: a centred
  circle needs k = m (X ∩ S = X), and a line through 0 gives k = 0 (two
  points).
- (a) Hypotheses:
  - `hm`: positive dimension.
  - `hXne`: nonempty.
  - `hXconn`: connected.
  - `hX`: smooth submanifold of ℝⁿ.
  - `hmn` is redundant (invariance of domain) but harmless.
  All of them constrain X as problem.md does.
- (b) Trivial cases:
  - One-point X cannot carry an (E m)-atlas with m > 0.
  - Empty X is excluded by `hXne`.
  - Constant radius (X ⊂ S_R): the conclusion holds with r = R and k = m.
  - X through the origin: positive r is still available.
  None of these makes the statement false or trivial. The conclusion is not
  automatic: when S is tangent, X ∩ S can be a figure-eight, which admits no
  such atlas, so r must be chosen.
- Truth check (the statement is not vacuous and is true): apply Sard to the
  smooth map ‖·‖² on the abstract manifold X. If it is constant, use X itself.
  Otherwise a regular value r² > 0 exists in the interior of the image, and
  its fibre is a C^∞ (m−1)-submanifold of X. The composite inclusion into ℝⁿ
  is smooth.
- Caveat: `IsEmbeddedSmoothSubmanifold` requires a C^∞ atlas on the subspace
  and a smooth inclusion, but no injective differential. For example, the
  cusp y² = x³ with chart t ↦ (t², t³) satisfies it without being a
  submanifold. The effects:
  - Hypothesis side: X is widened. This strengthens the statement, which
    stays true by the argument above.
  - Conclusion side: the predicate sits strictly between the prelim's literal
    "X ∩ S is a smooth manifold" and "smooth submanifold of ℝⁿ".
  I do not count this as a narrowing, because the prelim's own words ("is a
  non-empty smooth manifold") are met and exceeded. Adding
  `∀ x, Function.Injective (mfderiv … (↑) x)` to both predicates would make
  the notion exactly "embedded submanifold".
- Leftover code, which does not affect the statement:
  - The helper lemma `apm_t96j05_nontrivial_of_pos_dim` still assumes
    `[IsManifold (apm_t96j05_I m) ⊤ Y]` (analytic), so it cannot be applied
    to the C^∞ hypothesis as written.
  - `apm_t96j05_HasSmoothManifoldStructure` and `apm_t96j05_IsSmoothRadialLevel`
    are unused by the current theorem.

### t00A04 re-grade (commit e10380e8, working tree clean)

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00A04 | stronger (drops orientation, still true); otherwise faithful to the exactly corrected prelim | `apm_t00a04` | `[Nontrivial X]` replaces `[Nonempty X]` + `0 < finrank E`. This is exactly the set of X on which the prelim claim holds. C^∞ throughout, and nothing else is added | yes, real (X empty or one point); `[Nontrivial X]` is the exact correction and PRELIM-DEFECT.md now says so correctly |

The current binder is `[T2Space X] [CompactSpace X] [Nontrivial X]`. It carries
no dimension hypothesis, and everything else is as graded above. Smoothness is
`IsManifold I ∞`, `IsManifold J ∞` and `ContMDiff … ∞` (C^∞).

- **The correction is exact.** The prelim fails precisely when |X| ≤ 1:
  - X = ∅: the Lean definition `NullHomotopic` holds as soon as Y is nonempty.
  - X = {pt}: ι is constant.
  - |X| ≥ 2: the claim holds (next bullet). So `[Nontrivial X]` removes the
    counterexamples and nothing more.
- **The statement is true.**
  - Positive dimension: X is a nonempty closed n-manifold with n > 0. Some
    component has nonzero H_n(·; ℤ/2), and ι_* is injective on it because
    r ∘ ι = id. A null-homotopic ι would make ι_* zero in degree n > 0.
  - Dimension 0 in this encoding: finrank E = 0, so X is discrete (and finite,
    since it is compact). If H were a null-homotopy of ι, then for each x the
    path t ↦ r(H(x,t)) is continuous into discrete X, hence constant. So
    x = r(y) for every x, which contradicts `Nontrivial X`.
  - Dimension is fixed by the single model E, so X has no mixed-dimension
    case.
- **Nothing else is narrower.**
  - "X ⊂ Y" is encoded as a smooth ι with a smooth left inverse. dι is
    injective and X compact, so ι is an embedding: equivalent to the prelim.
  - `I, J` are arbitrary `ModelWithCorners ℝ E E`, which have open range by
    invariance of domain, so the manifolds have no boundary.
  - Orientation of X and Y is dropped. This strengthens the statement and it
    stays true (the mod-2 argument above).
  - I found no hypothesis that is always true or that is disconnected from
    the objects.
- **Trivial cases.**
  - Empty and one-point X are excluded by `Nontrivial`.
  - A constant ι is impossible given r ∘ ι = id and |X| ≥ 2.
  - A discontinuous ι is excluded by `C(X, Y)`.
  - A two-point X in a disconnected Y (for example Y = two circles, one point
    on each, r collapsing each circle): the hypotheses are satisfiable and the
    conclusion holds, since the points lie in different path components.
- **Remaining nit (docs only).** The module docstring "Statement repairs" still
  says "The source omits positive dimension … We add … its identity is not
  homotopic to a constant map". That describes the superseded encoding, not
  `[Nontrivial X]`. The theorem docstring and PRELIM-DEFECT.md are current.

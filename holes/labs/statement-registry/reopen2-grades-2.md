# Second-pass grades 2: t00J06, t94J08, t96J07

Read-only grade of the current `theorem apm_<id>` in /home/joe/code/apm-lean at HEAD `3a0c6180` (working tree clean for these three bundles). Commits graded: t00J06 `9bef8f8b`, t94J08 `ad725e36` + `331cce55`, t96J07 `7cc85a8b`. Nothing was built or run; `apm_<id>_previous_encoding` was ignored. Smoothness notation: all three files `open scoped ContDiff`, so `∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)` (C^∞). No current statement uses a bare `⊤` as an order.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00J06 | faithful | `apm_t00j06` | S is now a compact, Hausdorff, connected, boundaryless smooth 2-manifold (`ChartedSpace (EuclideanSpace ℝ (Fin 2))`, `IsManifold 𝓘(ℝ,E) ∞`) with H₀,H₁,H₂ = ℤ,ℤ⁴,ℤ. By classification that is exactly the closed oriented genus-2 surface. The conclusion is a connected cover with infinite fibres and a continuous lift | no |
| t94J08 | faithful | `apm_t94j08` | `hv` is now C^∞ (`∞`). The m = 0 case is genuine: an isolated zero of `v : ℝ → ℝ` with index (sign v(p+r) − sign v(p−r))/2, i.e. the reduced degree on {p±r}. The n = 0 case is a correct reduced-H₀ degree, but on a hand model (`Fin 2`, `Equiv.swap`, augmentation kernel of ℤ²), not on `T94J08Sphere 1` or singular homology | partial: degree on S⁰ only makes sense after choosing reduced homology. That excuses the hand model for n = 0. It does not excuse anything else |
| t96J07 | narrower (local-index conjuncts are vacuous) | `apm_t96j07` | f, the fixed points and L(f) are genuine: L is the alternating trace of f_* on rational singular homology, and the supplied isomorphisms are bases, not answers. But `apm_t96j07_HasLocalLefschetzNumber f q d` evaluates `chart.symm` outside `chart.target` and has no isolation or small-r condition. It therefore holds for every integer d, so the four local-index values state nothing | no |

## Evidence

### t00J06
```lean
theorem apm_t00j06
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    [ChartedSpace apm_t00J06_E S]
    [IsManifold (𝓘(ℝ, apm_t00J06_E)) ∞ S]
    (hS : apm_t00J06_hasGenusTwoHomology S)
    (f : C(apm_t00J06_Torus, S)) :
    ∃ (X : Type*) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (p : X → S),
      IsCoveringMap p ∧ (∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite) ∧
      ∃ lift : C(apm_t00J06_Torus, X), ∀ x, p (lift x) = f x
```
**(e) Is S a genuine closed genus-2 surface?** Yes.
- The model is `𝓘(ℝ, EuclideanSpace ℝ (Fin 2))`, which is boundaryless. Together with `CompactSpace` and `T2Space`, this makes S a closed topological 2-manifold (second countability follows from compact + locally Euclidean). `PathConnectedSpace` makes it connected.
- `hasGenusTwoHomology` gives H₂ ≅ ℤ, so S is orientable (a non-orientable closed surface has H₂ = 0). It also gives H₁ ≅ ℤ⁴, so the genus is 2. By classification, S ≅ Σ₂.
- The smooth structure is extra but harmless: every closed surface admits one. The order is `∞`, not analytic.
- This closes the earlier grader's gap (no manifold hypothesis). The homology hypotheses now only pick the genus within closed surfaces.

**Other hypotheses.** The source says "any map", and f is required to be continuous. That is the standard reading, since lifting is a topological notion.

**Conclusion.** The cover is connected (this repairs the disconnected `S × ℕ` loophole), fibres are infinite, `IsCoveringMap` is Mathlib's, and the lift is continuous. This is the prelim's "infinite covering". The statement is true: f_*(π₁T²) is an abelian subgroup of π₁Σ₂, hence cyclic, hence of infinite index. The associated cover is connected, infinite-sheeted, and f lifts to it.

**(b) Trivial cases.**
- Empty S: excluded by `PathConnectedSpace`.
- One-point S: excluded by H₁ ≅ ℤ⁴ and by the chart model.
- Constant f: it lifts to the universal cover, which is consistent with the prelim.
- Discontinuous f: excluded by `C(·,·)`.
- Nothing makes the statement trivially true: the conclusion still needs a connected infinite cover and a genuine lift.

### t94J08
```lean
theorem apm_t94j08 :
    t94J08HasReducedDegreeZero (Equiv.swap (0 : Fin 2) 1) (-1) ∧
    (∀ n : ℕ, 1 ≤ n → t94J08HasDegree n t94J08Antipodal ((-1 : ℤ) ^ (n + 1))) ∧
    (∀ (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (p r : ℝ) (d : ℤ),
      t94J08HasLocalIndexOne v p r d →
      t94J08HasLocalIndexOne (fun x ↦ -v x) p r (-d)) ∧
    ∀ (m : ℕ) (hm : 1 ≤ m) (v : …) (hv : ContDiff ℝ ∞ v) (p : …)
      (hp : t94J08HasIsolatedZero v p) (r : ℝ) (hr : 0 < r) (hlink …) (hlinkNeg …) (d : ℤ),
      t94J08HasLocalIndex v p r hlink d →
      t94J08HasLocalIndex (fun x ↦ -v x) p r hlinkNeg ((-1 : ℤ) ^ (m + 1) * d)
```
**(c) Smoothness.** Both `hv` use `∞` (C^∞). The analytic restriction is gone.

**(d) The m = 0 case is genuine.**
```lean
def t94J08HasLocalIndexOne (v : ℝ → ℝ) (p r : ℝ) (d : ℤ) : Prop :=
  v p = 0 ∧ 0 < r ∧ (∀ x, dist x p < r → x ≠ p → v x ≠ 0) ∧
    v (p - r) ≠ 0 ∧ v (p + r) ≠ 0 ∧
    (d : ℝ) = (Real.sign (v (p + r)) - Real.sign (v (p - r))) / 2
```
- Commit `331cce55` added "p is the only zero in the closed r-interval". With that, the formula is the standard 1-dimensional index: the reduced degree of v/|v| on the boundary {p−r, p+r}.
- The formula mentions v itself, and d is pinned to {−1, 0, 1}.
- The premise is satisfiable, e.g. v(x) = x − p gives d = 1. The conclusion −d = (−1)^1·d matches (−1)^n·d with n = 1.
- The zero field fails the isolation clause, as it should.
- The m ≥ 1 branch no longer has to cover dimension 1, which was the earlier vacuity.

**(d) The n = 0 case: correct reduced degree, on a hand model.**
```lean
def t94J08HasReducedDegreeZero (f : Equiv.Perm (Fin 2)) (d : ℤ) : Prop :=
  ∀ a : Fin 2 → ℤ, a 0 + a 1 = 0 → a (f.symm 1) - a (f.symm 0) = d * (a 1 - a 0)
```
- This is the action of f_* (a ↦ a ∘ f.symm) on the augmentation kernel ℤ·(e₁ − e₀), which is H̃₀ of a two-point space. It pins d uniquely: the identity forces d = 1 and swap forces d = −1. So it is a degree statement, not the earlier bare swap fact.
- However, S⁰ appears only as `Fin 2` with the antipodal map as `Equiv.swap`. The statement does not use `T94J08Sphere 1`, `t94J08Antipodal` or singular homology, and the conjunct is closed arithmetic.
- The prelim does not say which degree it means on S⁰, and any honest n = 0 answer needs reduced homology. For that reason I accept the model as a reasonable encoding. The identification S⁰ ≅ Fin 2 is the author's, not something proved.

**m ≥ 1 and n ≥ 1.** Unchanged from pass 1 apart from `∞`. Degrees are on actual integral singular top homology of the metric spheres, and the answer (−1)^(n+1) is correct.
- `hlink` does not require r < ε (no other zero inside the r-sphere). Because the claim quantifies over all r, it covers the small-r local index. It is also true for every r (it is a statement about the degree of the link map). So this makes the branch stronger, not wrong.
- Working in a chart ℝ^(m+1) is acceptable: negation commutes with the chart representation.
- A 0-dimensional manifold (empty linking sphere) is not covered. I treat that as degenerate and do not count it as a drop.

**(b) Trivial cases.**
- The zero field has no isolated zero, so both branches' premises fail for it, as they should.
- A constant nonzero field fails `v p = 0`.
- v(x) = x − p in dimension 1 gives d = 1 ↦ −1, which is correct.
- No hypothesis is always true, and none omits v.

### t96J07
```lean
theorem apm_t96j07 :
    ∃ f : C(apm_t96j07_RP3, apm_t96j07_RP3),
      (∀ x hx, f (mk x) = mk (A x)) ∧ (∀ q, f q = q ↔ ∃ i, q = mk (axis i)) ∧
      apm_t96j07_HasLocalLefschetzNumber f (mk (axis 0)) (-1) ∧ … (axis 1) 1 ∧
      … (axis 2) (-1) ∧ … (axis 3) 1 ∧
      apm_t96j07_HasLefschetzNumber f 0
```
**Genuine parts.**
- `f` is pinned by its values on `mk x` (mk is surjective), is continuous on the quotient-topology RP³, and its fixed points are exactly the four axes.
- `HasLefschetzNumber f 0` is ∃ bases e0…e3 with HQ₀ ≅ ℚ, HQ₁ ≅ ℚ^0, HQ₂ ≅ ℚ^0, HQ₃ ≅ ℚ, and L = tr₀ − tr₁ + tr₂ − tr₃ of the conjugated f_* on actual rational singular homology.
- **(a) The isomorphisms do not prescribe the answer.** Trace is conjugation-invariant. The isomorphisms only record the true Betti numbers (1, 0, 0, 1) of RP³, which is itself something to prove. The value 0 comes from f_* on H₀ and H₃, i.e. from f (f ≃ id through positive diagonal matrices, so L = 1 − 1).
- This fixes the pass-1 defect `((1:ℤ) - 1) = 0`.

**Local indices: vacuous.** The new predicate is
```lean
∃ chart : OpenPartialHomeomorph apm_t96j07_RP3 apm_t96j07_E3,
  q ∈ chart.source ∧ chart q = 0 ∧ ∃ r, 0 < r ∧ ∃ link : C(S2, S2),
    (∀ x, chart.symm (r • x.1) ∈ chart.source ∧ f (chart.symm (r • x.1)) ∈ chart.source ∧
      ∃ hne : r • x.1 - chart (f (chart.symm (r • x.1))) ≠ 0, link x = normalize(…)) ∧
    ∃ orientation : H₂(S²) ≅ ℤ, ∀ a, orientation.hom (link_* a) = d * orientation.hom a
```
It does mention f, which is progress. It has two gaps:
1. It never requires `r • x.1 ∈ chart.target`. `OpenPartialHomeomorph` constrains `invFun` only on `target` (continuity and inverse laws), so `chart.symm` on the sphere can be any function.
2. There is no condition that q is the only fixed point in the r-ball.

**Counterexample: any d is achievable at q = [e₀].**
- Setup:
  - Take the affine chart φ[1, y] = y, where f reads y ↦ Dy with D = diag(2, 3, 4).
  - Restrict the source so that `target = ℝ³ \ rS²`.
  - On rS², redefine `invFun (r x) := φ⁻¹(D⁻¹ v(x))` with v(x) = r x − R·m(x), where m : S² → S² has degree d and R > 5r.
- Every clause holds:
  - |v| ≥ R − r > r and |D⁻¹v| ≥ (R − r)/4 > r, so `chart.symm (r x)` and `f (chart.symm (r x)) = φ⁻¹(v x)` both lie in the source.
  - The displacement is r x − v(x) = R·m(x) ≠ 0.
  - Hence `link = m`, which has degree d.
- So `HasLocalLefschetzNumber f [e₀] d` holds for every d ∈ ℤ. In particular it holds for +1, while the true index is −1. The same construction works at each axis.
- The four local conjuncts are therefore true whatever the local indices are, and they state nothing about them.

Even with the target condition added, the lack of isolation matters. A chart can be centred at [e₀] on RP³ minus a plane avoiding [e₀] and [e₁] (e.g. {x₀ + x₁ = 0}), and a large sphere in that chart can pick up several fixed points. That is harder to realise here because f(sphere) must stay in the source, but the definition does not exclude it.

**Fix (not applied).** Add `r • x.1 ∈ chart.target` for all x on the sphere, and require that no other fixed point lies in `chart.symm '' closedBall 0 r`. Alternatively, require the closed r-ball to lie in the target and q to be the only fixed point in its image. Then d is the fixed-point index, and the values −1, 1, −1, 1 would be real content.

**(b) Trivial cases.** f is existential but pinned, so there are no constant or discontinuous substitutes. RP³ is nonempty. The defect found by the trivial-construction check is the junk-value chart above.

The prelim is not defective.

### t96J07 re-grade

This re-grades `apm_t96j07` at commit `b7d38e96` ("local index requires the r-ball in the chart target, mapped back into the source, isolating q"). The working tree for the bundle is clean. The theorem text is unchanged; only `apm_t96j07_HasLocalLefschetzNumber` changed.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t96J07 | faithful | `apm_t96j07` | The local predicate now requires `closedBall 0 r ⊆ chart.target`, requires f to carry `chart.symm` of that ball into `chart.source`, and makes 0 the only fixed point of F = chart ∘ f ∘ chart.symm in the ball. The link degree is then the fixed-point index of f at q, which does not depend on the chart, its orientation, r or the orientation isomorphism. f, the fixed points and L(f) were already genuine. The whole statement is true | no |

**The new clauses.**
```lean
Metric.closedBall (0 : apm_t96j07_E3) r ⊆ chart.target ∧
(∀ y ∈ Metric.closedBall (0 : apm_t96j07_E3) r, f (chart.symm y) ∈ chart.source) ∧
(∀ y ∈ Metric.closedBall (0 : apm_t96j07_E3) r, chart (f (chart.symm y)) = y → y = 0) ∧
```
- **They kill my construction.** The linking sphere r·S² now lies inside the closed ball, which is inside `chart.target`. On the target, `chart.symm` is the genuine continuous inverse, so there is no room to redefine it on the sphere.
- **F is a real continuous map.** By the second clause, F = chart ∘ f ∘ chart.symm is defined and continuous on the closed ball: `chart.symm` is continuous on the target, f is continuous, and `chart` is continuous on the source.
- **The displacement is nonzero on the sphere.** The isolation clause says F has no fixed point on the ball except 0. So y − F(y) ≠ 0 on r·S², and the `hne` clause is implied.
- **d is the index.** The degree of (y − F y)/|y − F y| on ∂B is by definition the fixed-point index of F on B (Dold's definition). By isolation, that is the local index of f at q.
- **A wrong d is impossible.** If two witnesses gave d ≠ d', they would contradict well-definedness of the index. I found no other construction that gives a wrong d:
  - The earlier multi-fixed-point chart is excluded by isolation.
  - Degenerate charts are excluded because q ∈ source, `chart q = 0` and r > 0 force a genuine open 3-ball around q.

**Independence.**
- **Of r:** for r' < r, both valid, the annulus between the spheres has no fixed point, so the normalised displacement is homotopic across radii and the degrees agree.
- **Of the chart and its orientation:** the fixed-point index is a topological invariant (the commutativity axiom). For a reflection R, the conjugated displacement is y ↦ R·g(R y), of degree (−1)·deg g·(−1) = deg g. So an orientation-reversing chart gives the same d.
- **Of `orientation`:** any automorphism of ℤ is ±1 and commutes with scalar multiplication. So "link_* = multiplication by d" does not depend on the choice, as with `t94J08HasDegree_with_orientation`.

**The values are true.** Take the affine chart x_i = 1 translated to [e_i]. The other fixed points have x_i = 0, so they are outside the chart. A multiplies coordinates by positive scalars, so it preserves x_i ≠ 0; the second clause therefore holds for every r, and the target is all of ℝ³. In this chart F is linear, D = diag((j+1)/(i+1))_{j≠i}. The displacement is (I − D)y, whose degree is sign det(I − D):
- i = 0: (−1)(−2)(−3) = −6, so −1.
- i = 1: (1/2)(−1/2)(−1) > 0, so +1.
- i = 2: (2/3)(1/3)(−1/3) < 0, so −1.
- i = 3: (3/4)(1/2)(1/4) > 0, so +1.

This matches the statement's −1, 1, −1, 1.

**Consistency with L(f).** The indices sum to 0, which equals `HasLefschetzNumber f 0` (Lefschetz–Hopf). The trace definition of L(f) is independent of the indices, so the statement does not simply assert the sum.

**(b) Trivial cases.** f is existential but pinned by its values on `mk x`. Constant, identity and discontinuous substitutes are therefore unavailable. The junk-chart construction is blocked, as shown above.

The prelim is not defective.

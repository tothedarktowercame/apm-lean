# Re-open fidelity grades, second pass, batch 1 (current `theorem apm_<id>` only)

Graded read-only against `problems/<id>/problem.md` in /home/joe/code/apm-lean, 2026-09-28.
The statements graded are the ones at commits 35ee1d11 (t00A01), 37a25e20 (t02A01) and 236b5480 (t91A01).
`apm_<id>_previous_encoding` was ignored. Nothing was built or run.
Smoothness check: `.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:110-112`
defines `ω := (⊤ : WithTop ℕ∞)` and `∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)` under `open scoped ContDiff`.
t00A01 and t91A01 both open that scope and use `∞`, which means C^∞. t02A01 has no smoothness order.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00A01 | faithful | `apm_t00a01` | The summands are now compact, Hausdorff, second-countable, boundaryless C^∞ 3-manifolds, and `φᵢ` are topological embeddings. The earlier counterexamples (discontinuous bijection, whisker) are excluded. Allowing arbitrary (possibly wild) embeddings instead of a simplex is slightly more general, and it remains true | no |
| t02A01 | faithful | `apm_t02a01` | The base is a concrete quotient: a square annulus with opposite outer edges glued, i.e. a torus minus an open disk. `apm_t02a01_boundary` is the inner boundary circle, and the cover is an `IsCoveringMap` with a homomorphic `ZMod n` action by homeomorphisms that is simply transitive on fibres. The z ↦ z² counterexample no longer applies. Connectedness of S̃ is not required, and the claim is still true without it | no |
| t91A01 | false | `apm_t91a01` | The surface, the tangent field and C^∞ smoothness are now genuine. The index-3 hypothesis still does not constrain V: the frames `τ z` are an arbitrary linear isomorphism for each boundary point, with no continuity and no link to the chart. So any isolated zero satisfies it. Counterexample: S² with a smooth field having a single zero (index 2) | minor: "compact surface" has to be read as closed (the Lean statement assumes this) |

## Evidence

### t00A01
```lean
[T2Space M₁] [T2Space M₂]
[SecondCountableTopology M₁] [SecondCountableTopology M₂]
[CompactSpace M₁] [CompactSpace M₂]
[ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
[IsManifold apm_t00A01_Model3 ∞ M₁] [IsManifold apm_t00A01_Model3 ∞ M₂]
[BoundarylessManifold apm_t00A01_Model3 M₁] [BoundarylessManifold apm_t00A01_Model3 M₂]
(φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
(hφ₁ : Topology.IsEmbedding φ₁) (hφ₂ : Topology.IsEmbedding φ₂)
(hM₁ : apm_t00A01_isHomology3Sphere M₁) (hM₂ : apm_t00A01_isHomology3Sphere M₂) :
```
The conclusion is unchanged from the first pass, which already accepted it as an encoding: `π₁(X) ≃* π₁M₁ * π₁M₂` (`Monoid.Coprod`), and X has the singular homology of S³. X is `apm_t00A01_connectedSum`: the quotient topology on the disjoint union of the two punctured pieces `{x // x ∉ φ '' {|y| < 1}}`, glued along the boundary spheres by `EqvGen`.

(a) What each hypothesis constrains:
- The typeclass hypotheses make each Mᵢ a closed topological 3-manifold with a C^∞ structure. The order is `∞` (C^∞), not the bare `⊤` that means analytic.
- The problem asks for triangulated manifolds. In dimension 3 every closed topological manifold is both triangulable and smoothable (Moise), so the two classes agree up to homeomorphism. Using smooth manifolds is a reasonable encoding choice.
- `hMᵢ` states the homology condition that problem.md defines. It also forces Mᵢ to be connected, since H₀ ≅ ℤ.
- `hφᵢ` makes the disk map continuous and a homeomorphism onto its image.

(b) Trivial cases and the earlier counterexamples:
- Empty M: excluded, because `hM` needs H₀ ≅ ℤ.
- One-point M: excluded, because it has no chart onto an open subset of ℝ³.
- Constant φ, or a discontinuous bijection D³ → S³ (the earlier counterexample): excluded, because φ must be an embedding.
- S³ with a whisker attached (the earlier H₀ counterexample): excluded, because it is not a manifold.

(d) Truth. The prelim lets you assume φᵢ(D³) is a simplex. The Lean statement allows any topological embedding, including wild ones such as the Alexander horned ball. I checked that the statement still holds for those:
- φ(int D³) is open in M by invariance of domain, so Pᵢ = Mᵢ \ φᵢ(int D³) is closed.
- Mᵢ = Pᵢ ∪ φᵢ(D³), and Mᵢ, φᵢ(D³) and the intersection S² are all ANRs. By Borsuk's theorem on closed unions, Pᵢ is then an ANR.
- The inclusion S² ⊂ Pᵢ is therefore a cofibration. That makes both Mᵢ = Pᵢ ∪_{S²} D³ and X = P₁ ∪_{S²} P₂ homotopy pushouts.
- Van Kampen on Mᵢ gives π₁Pᵢ ≅ π₁Mᵢ. The same argument on X gives π₁X ≅ π₁P₁ * π₁P₂.
- Mayer–Vietoris on Mᵢ, with the local-homology check that H₃(M) → H₂(S²) is an isomorphism, shows each Pᵢ is a homology ball. Mayer–Vietoris on X then gives H(X) ≅ H(S³).

So the Lean statement is slightly more general than the prelim and still true. I grade it faithful.

The base point of X is the image of an arbitrary boundary point, and mᵢ is arbitrary. Both choices are harmless because the spaces are path-connected.

### t02A01
```lean
abbrev apm_t02a01_squareAnnulus :=
  {x : ℝ × ℝ // x.1 ∈ Set.Icc 0 1 ∧ x.2 ∈ Set.Icc 0 1 ∧ (1 / 4 : ℝ) ≤ ‖x - (1 / 2, 1 / 2)‖}
-- edgeRel: (0,y) ~ (1,y) and (x,0) ~ (x,1); puncturedTorus := Quotient (EqvGen.setoid edgeRel), coinduced topology
def apm_t02a01_boundary := mk '' {x | ‖x.1 - ((1 / 2, 1 / 2) : ℝ × ℝ)‖ = (1 / 4 : ℝ)}
theorem apm_t02a01 {Stilde : Type*} [TopologicalSpace Stilde]
    (p : Stilde → apm_t02a01_puncturedTorus) (n : ℕ) (hn : 0 < n)
    (hcover : IsCoveringMap p) (hp_surjective : Function.Surjective p)
    (deck : ZMod n → Homeomorph Stilde Stilde)
    (hdeck_zero : deck 0 = Homeomorph.refl Stilde)
    (hdeck_add : ∀ z w, deck (z + w) = (deck z).trans (deck w))
    (hdeck_over : ∀ z x, p (deck z x) = p x)
    (hdeck_transitive : ∀ x y, p x = p y → ∃! z, deck z x = y) :
    Nat.card (ConnectedComponents (p ⁻¹' apm_t02a01_boundary)) = n
```
(a) What each hypothesis constrains:
- The base S is now fixed.
  - The norm on `ℝ × ℝ` is the sup norm, so the removed "open disk" is the open square (1/4, 3/4)². That is still homeomorphic to a disk, so S is [0,1]² minus an open square.
  - The edge relation glues exactly the opposite outer edges; the four corners become a single point. The `h₀/h₁` side conditions always hold on outer edges, since those points are at sup-distance 1/2 from the centre. The quotient carries the quotient topology. So S is a torus minus an open disk.
  - `apm_t02a01_boundary` is the image of the inner square boundary. It lies away from the glued edges, so the quotient map is injective on it, and it is the actual boundary circle.
- `hcover` and `hp_surjective` make p a genuine covering with nonempty fibres.
- `deck` is a group homomorphism into homeomorphisms over p that is simply transitive on each fibre. So p is a principal ZMod n–cover and every fibre has n points.

(b) Trivial cases and the earlier counterexample:
- Empty S̃: excluded by surjectivity.
- The earlier counterexample (S¹ double cover with boundary = univ): excluded, because the base and boundary are now fixed.
- Discontinuous deck maps: excluded, because they are `Homeomorph`s.

(d) Truth.
- Monodromy on the fibre over a boundary point commutes with the simply transitive ZMod n action, so it acts by translations. This gives a homomorphism π₁(S) = F(a,b) → ZMod n.
- The boundary loop is the commutator [a,b], so it maps to 0. Hence p⁻¹(∂S) is a trivial n-sheeted cover of the circle and has n components.
- This argument does not use connectedness of S̃, which the Lean statement omits and a "regular covering" would normally include. The omission makes the statement slightly more general, and it is still true.

Faithful.

### t91A01
```lean
∀ (F : Type*) [TopologicalSpace F] [T2Space F] [SecondCountableTopology F] [CompactSpace F]
  [ConnectedSpace F] [ChartedSpace apm_t91a01_E2 F] [IsManifold apm_t91a01_Model2 ∞ F]
  [BoundarylessManifold apm_t91a01_Model2 F] (hOrient : apm_t91a01_oriented F)
  (V : (x : F) → TangentSpace apm_t91a01_Model2 x) (p : F),
  ContMDiff apm_t91a01_Model2 apm_t91a01_Model2.tangent ∞ (fun x ↦ (⟨x, V x⟩ : TangentBundle _ F)) →
  V p = 0 → (∃ U ∈ nhds p, ∀ q ∈ U, V q = 0 → q = p) →
  apm_t91a01_hasIndexThreeZero V p → ∃ q : F, q ≠ p ∧ V q = 0
```
and
```lean
def apm_t91a01_hasIndexThreeZero V p : Prop :=
  ∃ (φ : apm_t91a01_Disk2 → F) (hφ : Topology.IsEmbedding φ), φ ⟨0, _⟩ = p ∧
    ∃ (τ : ∀ z : apm_t91a01_Circle, TangentSpace apm_t91a01_Model2 (φ ⟨z.1, _⟩) ≃L[ℝ] ℂ)
      (hnz : ∀ z, τ z (V (φ ⟨z.1, _⟩)) ≠ 0) (link : C(apm_t91a01_Circle, apm_t91a01_Circle)),
      (∀ z, link z = apm_t91a01_localDirection V φ τ hnz z) ∧ ∀ z, link z = ⟨z.1 ^ 3, _⟩
```
Part (a), the z³ model, is unchanged and was accepted in the first pass.

In part (b) the surface, the tangent section V and the smoothness are genuine, with order `∞` (C^∞). The defect is the index hypothesis:
- `τ z` is a separate continuous linear equivalence T_{φ(z)}F ≃ ℂ chosen for each boundary point z. Nothing requires it to vary continuously in z, or to come from the chart, from φ, or from the derivative of φ.
- Since GL₂(ℝ) acts transitively on nonzero vectors, one can pick τ z so that τ z (V(φ z)) = z³ for every z. Then `localDirection` is z ↦ z³, which is continuous, so `link` exists.
- So `hasIndexThreeZero V p` holds for any V that is nonzero on the boundary of some embedded disk centred at p. That includes every isolated zero, whatever its index. The hypothesis is still not computed from V at p.
- Requiring τ to be continuous would not be enough either. A loop in GL₂(ℝ) can have nonzero winding, which shifts the degree of the direction map. The frames need to be tied to the chart, i.e. to a fixed trivialization of TF over the disk.

**Counterexample.**
- F = S² with Mathlib's C^∞ structure. It is compact, T2, second countable, connected and boundaryless, and orientable.
  - `hOrient` only needs some atlas of partial homeomorphisms to E2 with positive-determinant transition derivatives. Stereographic charts with one of them reflected provide one.
- V = the "dipole" field: the pushforward of a constant field on ℝ² under inverse stereographic projection from p. It is smooth and has exactly one zero, at p, of index 2.
- For φ, take a small coordinate disk centred at p. V is nonzero on its boundary circle; choose τ as above.
- Every hypothesis holds, and V has no second zero, so the statement is false.

Trivial cases: F a point is now excluded, since it has no chart to ℝ². V = 0 is excluded because its zero at p is not isolated.

Prelim note: problem.md says "compact, oriented surface". The claim needs the surface to have no boundary: on a closed disk, z³ has only one zero. The Lean statement's `BoundarylessManifold` is the right reading, so this is a reading of the prelim, not a departure from it.

Fix direction: take the index from V itself. For example, fix a chart (or φ smooth with `mfderiv`) and use the trivialization it induces on the tangent spaces over the disk, then require the degree of V/|V| on the boundary circle in that trivialization to be 3. Alternatively, require `τ` to be the chart's `TangentSpace` identification rather than an arbitrary equivalence.

### t91A01 re-grade (commit d06c0d02)

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t91A01 | narrower (mild), true | `apm_t91a01` | The index hypothesis now reads V through the chart at p, so it depends on V, and the dipole counterexample fails. It asks for the exact direction z ↦ z³ on a circle in the fixed chart `chartAt p`, not index 3: a zero of index 3 whose direction is only homotopic to z³ is not covered | minor, as before: "compact" has to be read as closed |

```lean
def apm_t91a01_chartField V p y :=
  mfderiv 𝓘 𝓘 (extChartAt 𝓘 p) ((extChartAt 𝓘 p).symm y) (V ((extChartAt 𝓘 p).symm y))
def apm_t91a01_hasIndexThreeZero V p : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.closedBall (extChartAt 𝓘 p p) r ⊆ (extChartAt 𝓘 p).target ∧
    ∀ z : Circle, ∃ hw : planeEquiv.symm (chartField V p (circlePoint p r z)) ≠ 0,
      planeEquiv.symm (chartField …) / ‖planeEquiv.symm (chartField …)‖ = z.1 ^ 3
```

**Does the hypothesis depend on V, and is mfderiv meaningful?** Yes, on both counts.

The value of `mfderiv`:
- The closed ball lies in the chart's target, so every circle point y maps under `(extChartAt p).symm` to a point x in `(chartAt p).source`.
- In Mathlib, `TangentSpace 𝓘 x` is the model space, expressed in the chart `chartAt x`.
- `mfderiv (extChartAt p) x` is computed as the ordinary derivative of `extChartAt p ∘ (extChartAt x).symm` at `extChartAt x x`. That is the derivative of the transition map from the chart at x to the chart at p.
- So `chartField V p y` is V at x, written in the coordinates of the chart at p. There is no junk value here.

Why the derivative exists:
- `extChartAt p` is differentiable on its source when the manifold is at least C¹ and has no boundary. Here it is `IsManifold 𝓘 ∞` and `BoundarylessManifold`, and the model is `𝓘(ℝ, E2)`, whose range is all of E2.
- No further hypothesis is needed.

What the hypothesis now says:
- `ContMDiff … ∞` on the section makes y ↦ chartField V p y continuous (indeed smooth) on the chart target. The order is `∞`, i.e. C^∞, not analytic.
- So the hypothesis says: the chart-read field has no zeros on the circle of radius r about the image of p, and its normalized direction there is exactly z³. That fixes the winding number of V on that circle to be 3.
- There are no free frames left, unlike the `τ` of the previous version.

**Counterexamples.** None survive.
- Dipole on S², the earlier counterexample:
  - The chart at p is stereographic projection from −p, and it sends p to 0. On every circle about 0 the field winds twice.
  - A continuous map of the circle that equals z³ has degree 3, so no r works and the hypothesis fails.
  - This is exactly how the hypothesis should behave.
- V = 0: `hw` fails.
- One-point or empty F: excluded, because a chart to ℝ² is required and p ∈ F.
- Index-0 zero on T² (the field f·X): it winds 0 on small circles, and on larger circles only if other zeros are enclosed. In that case a second zero exists and the conclusion holds.

The hypothesis is also satisfiable, so the statement is not vacuous. Take V equal to the chart-read field z³ near p, cut it off, and add any field away from the disk. The resulting V has other zeros, as it must.

**Truth.** Suppose p were the only zero of V.
- Then the winding number on the circle equals ind_p(V), so ind_p(V) = 3.
- Poincaré–Hopf gives ind_p(V) = χ(F), and a connected closed surface has χ(F) ≤ 2. Contradiction.
- If the disk contains other zeros, the conclusion holds directly.
- The absence of an "only zero in the disk" condition is harmless, as claude-18 says.
- Reversing a chart's orientation conjugates the direction map by complex conjugation, which leaves its degree unchanged. So the argument does not depend on the orientation of the chart at p.

The statement is true.

**`apm_t91a01_oriented`: it does not affect truth, and it is consistent with the prelim.**
- It asks for some atlas of homeomorphisms to E2 whose transition maps have positive Jacobian determinant at every point.
- `fderiv` of the total function `d ∘ c.symm` is the real derivative near c x, because c.source ∩ d.source is open. If the transition is not differentiable, `fderiv` returns 0, and a positive determinant rules that out.
- Such an atlas makes F topologically orientable: a differentiable map with invertible derivative has local degree equal to the sign of the determinant. Orientable surfaces have such an atlas, e.g. an orientation-compatible subatlas of the smooth structure. So the condition is satisfiable and means "oriented", as the prelim says.
- Poincaré–Hopf and χ ≤ 2 also hold for non-orientable closed surfaces, so the claim would stay true without it.
- It is not tied to the `ChartedSpace` structure. That does no harm here.

**Why the grade is narrower rather than faithful.**
- Part (b) assumes "a zero as in part (a)", i.e. an isolated zero of index +3.
- The Lean hypothesis asks for more than index 3. The normalized direction must be exactly z ↦ z³ on some circle, in the one chart `chartAt p` that the `ChartedSpace` instance supplies.
- A zero of index 3 whose chart direction is only homotopic to z³ does not satisfy the hypothesis. An example is z³ composed with a reparametrization of the circle, or a field such as z³ + (small non-radial perturbation).
- So the Lean statement covers a subclass of index-3 zeros.
- Reading "as in part (a)" literally as the z³ picture defends this choice, and the proof is the same. The narrowing is still an extra hypothesis, and the prelim does not force it.

**Fix (one line).** Replace the equality with a homotopy. Package the direction map on the circle as a `C(Circle, Circle)` and require it to be `ContinuousMap.Homotopic` to z ↦ z³, or equivalently to have degree 3. With that change the fixed chart no longer matters, because the index does not depend on the chart, and the statement would be faithful.

### t91A01 re-grade 2 (commit ec262416)

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t91A01 | faithful | `apm_t91a01` | The index hypothesis now says: the chart-read field has no zeros on some circle about p that lies in the chart, and its normalized direction there is a continuous self-map of the circle homotopic to z ↦ z³, i.e. of degree 3. This is exactly "p is a zero of index +3". The statement is true by Poincaré–Hopf | minor, as before: "compact" has to be read as closed, and Lean assumes this |

```lean
∃ r : ℝ, 0 < r ∧ Metric.closedBall (extChartAt 𝓘 p p) r ⊆ (extChartAt 𝓘 p).target ∧
  ∃ link : C(Circle, Circle),
    (∀ z, ∃ hw : planeEquiv.symm (chartField V p (circlePoint p r z)) ≠ 0,
       (link z).1 = w / ‖w‖) ∧
    ContinuousMap.Homotopic link apm_t91a01_cube
```

The rest of the statement is unchanged from re-grade 1:
- the surface: `IsManifold 𝓘 ∞`, boundaryless, compact, T2, second countable, connected;
- the orientation certificate;
- the C^∞ section `ContMDiff … ∞` (`∞`, not analytic);
- the reading `chartField` of V through `mfderiv (extChartAt p)`.

The findings of re-grade 1 on those parts still apply. `mfderiv` is a real derivative at the circle points. The hypothesis depends on V alone, since no frames are chosen by hand. `hOrient` means oriented and does not affect truth.

**Now faithful: every zero of index +3 satisfies the hypothesis.**
- Given an isolated zero p of index 3, pick r small enough that the closed disk lies in the chart target and contains no other zero. Isolation provides such an r.
- The winding number of the chart-read field on that circle is ind_p(V) = 3. Reversing the chart's orientation conjugates the direction map, which leaves its degree unchanged, so this holds in `chartAt p` whatever its orientation.
- Free homotopy classes of maps S¹ → S¹ are classified by degree, so the direction map is `Homotopic` to z³.
- Conversely, the hypothesis forces winding 3 on that circle. The narrowing found in re-grade 1 (exact equality with z³ in one fixed chart) is gone.

**Counterexamples.**
- `link` is forced pointwise to equal the direction map. Its continuity adds nothing, and it cannot be chosen freely.
- Dipole on S²: winding 2 on every chart circle, and 2 ≠ 3, so the hypothesis fails.
- V = 0: `hw` fails.
- One-point or empty F: excluded, because a chart to ℝ² is required.
- Index-0 zero on T²: it winds 0 unless the circle encloses other zeros, and then the conclusion holds.
- The hypothesis is satisfiable, e.g. by a chart-local z³ extended with a cutoff.

**Truth.**
- If p were the only zero of V, the disk would contain no other zero. The winding would then be ind_p = 3 = χ(F) by Poincaré–Hopf, but χ(F) ≤ 2 for a connected closed surface. Contradiction.
- If the disk encloses other zeros, a second zero exists outright.

The statement is true.

**Cosmetic.** The docstring of `theorem apm_t91a01` still says the direction is "`z ↦ z³`". The hypothesis now only needs a map homotopic to it. This does not affect the grade.

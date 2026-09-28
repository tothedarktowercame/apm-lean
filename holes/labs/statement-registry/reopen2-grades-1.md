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

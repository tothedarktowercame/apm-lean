# Statement-fidelity triage, list 3

Read-only triage. None of the 8 ids has an entry in `problems/STATEMENTS.json` (its `entries`/`revoked` contain none of them), and none has a `STATEMENT-REPAIR.md`. Repair notes are taken from the module docstrings in `Main.lean`.

| id | class | grade-or-gap | one-line reason |
|---|---|---|---|
| t97J07 | B | needs a part (c) conjunct; the rest is faithful | (a) is faithful: the fixed set is the line plus a point. (b) is a reasonable encoding as sign det(I-Dg) from real chart derivatives. (c) is only the arithmetic `2 + 1 = 3`; nothing ties it to χ(CP²). Add χ(CP²)=3 via Mathlib singular homology. The proof needs the Lefschetz theorem or H_*(CP²), which Mathlib lacks. |
| t98A01 | C | topological connected sum of surfaces; homeomorphism-invariant χ and its multiplicativity under covers | (a) conjunct 1 (the 5-fold torus cover) is a faithful "yes" by example. Conjunct 2 is extra (true) content. (b) is the arithmetic `connectedSum` plus `Homeomorph.refl`, i.e. vacuous. A narrower faithful part exists: (a) = conjunct 1. |
| t98A04 | B | under-strong submersion predicate (existential atlases) | The fibers, the fiber over [1,0] and the no-section claim (codomain correctly repaired to S³) are faithful and true. The "submersion" is quantified over arbitrary atlases. Pin the source to Mathlib's sphere atlas. |
| t99A01 | B | stand-in; faithful statement expressible (quotient space + `FundamentalGroup` + `singularHomologyFunctor`) | The statement never mentions X, Y, Z. It only has presented groups and kernels of cellular boundary maps (H₂), and omits H₁ (the cokernels) and H₀. Proof gap: van Kampen and cellular homology. |
| t99A02 | B | stand-in; three conjuncts are near-vacuous | `of i ^ 2 = 1` holds because the relation is literally in the set. Only "Z * Z/2 is infinite" has content, and the infinitude of π₁(RP²∨RP²) is missing. Faithful content: an explicit simply-connected covering model (expressible but heavy). At minimum, state both π₁ groups up to isomorphism. |
| t99A03 | B | stand-in; generic deck-transformation lemma | It is true but mentions neither space. (a) is absent. Both parts are expressible: RP² via `Projectivization` with the coinduced topology, the wedge via a quotient of a Σ-type, and #⁴RP² = repo `Surface false 4`. Proof gap for (a): the Lefschetz fixed-point theorem. |
| t99A04 | C | differential forms on manifolds (closed 1-forms, pullback, ∫ over S¹, Stokes/de Rham) | The statement is two 1-D calculus facts and never mentions X, f or η. Narrower faithful part: (b) on the flat torus `UnitAddCircle²`, with forms as periodic coefficient functions and the period of `dx` along the nonseparating x-loop being 1 ≠ 0. |
| t99J03 | B | **FALSE as written** (the sphere is missing) | `Surface true 0` is the closed disk: the edge relation is empty when genus = 0. So X = S² (`Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`, which has the `IsManifold (𝓡 2) ω` instance) matches neither branch. Also, (c) is a definitional tautology. |

## Evidence notes

### t97J07
- Part (a) is faithful and true. The 1-eigenspace of diag(1,1,3) gives the line {z₂=0}, and the 3-eigenspace gives the point [0:0:1]. The representative-dependence of `rep` is harmless because "a coordinate is zero" does not depend on scaling:
  ```lean
  {p : T97J07CP2 | t97J07Map p = p} = t97J07FixedLine ∪ {t97J07IsolatedPoint}
  def t97J07FixedLine : Set T97J07CP2 := {p | p.rep 2 = 0}
  ```
- Part (b): the charts are checked against the actual map (`t97J07LineChart_map`, `t97J07PointChart_map`). The indices are `sign (normSq (1 - Df))`, which is the real determinant of I − Dg for a ℂ-linear Dg. The values check out: det 4 for the line, giving index 1, and det (2/3)⁴ = 16/81 for the point, giving index 1. The line's contribution hard-codes χ(CP¹)=2 (`t97J07LineContribution := 2 * ...`). That is acceptable, since the problem itself is loosely posed: the fixed points on the line are not isolated, so a "local Lefschetz number of each fixed point" only makes sense per component.
- Part (c) is missing. The final conjunct `t97J07LineContribution + t97J07IndexFromDet t97J07PointDet = 3` is arithmetic about defined numbers. Smallest change: add `∑_{n≤4} (-1)^n finrank ℚ (H_n(CP²;ℚ)) = 3` using `singularHomologyFunctor`, with CP² given the quotient topology. That is a statement, not a proof, so this is B rather than C. The proof gap is the Lefschetz fixed-point theorem or the homology of CP².
- Nothing in it is false.

### t98A01
- (a) The example in conjunct 1, `t98A01IsRegularNfoldCover 5 t98A01TorusFiveCover` on `UnitAddCircle × UnitAddCircle` with `(x,y) ↦ (5x,y)`, faithfully answers "yes". Regularity is encoded as deck transitivity on fibers, which is fine.
- Conjunct 2 is not asked for. It says only the torus works:
  ```lean
  ∀ (g h : ℕ) (p : Surface true g → Surface true h), t98A01IsRegularNfoldCover 5 p →
    Nonempty (Surface true g ≃ₜ Surface true h) → eulerCharacteristic true g = 5 * eulerCharacteristic true h ∧ g = 1 ∧ h = 1
  ```
  It is true even with the `Surface true 0` = disk quirk (the disk has no connected 5-sheeted cover and is not homeomorphic to a closed surface). But it needs χ multiplicativity under covers and invariance of genus under homeomorphism, neither of which is in Mathlib. It over-commits.
- (b) is vacuous as topology. `connectedSum` is `Bool × ℕ` arithmetic and `t98A01PrintedSurface_homeomorph` is `Homeomorph.refl` after `decide`. The arithmetic itself is right: 2 + 2·3 + 1 + 2 = 11 crosscaps, χ = −9. A faithful (b) needs a topological connected sum of surfaces and an invariant χ (the gap).

### t98A04
- The repair of ι : S² → S³ is correct.
- `apm_t98a04_fiber apm_t98a04_p10 = {z | z.1 1 = 0}`, the fibers `≃ₜ Circle` and equal to unit-scalar orbits, and `¬∃ i, Continuous i ∧ ∀ p, hopf (i p) = p` are all true and faithful. The no-section proof needs a Hopf, π₃ or homology obstruction, but that is a proof gap only.
- The problem is `apm_t98a04_IsSubmersion`, which is `∃ sourceCharts : ChartedSpace R3 S3, ∃ targetCharts : ChartedSpace R2 CP1, IsManifold … ∧ ContMDiff … ∧ ∀ z, Surjective (mfderiv …)`. This is submersion for *some* smooth structures, not the standard one. Smallest change: define S³ as `Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1` with `Fact (finrank ℝ _ = 3 + 1)`. Mathlib's `EuclideanSpace.instChartedSpaceSphere` / `instIsManifoldSphere` then fixes the source. The target atlas may stay existential: smooth structures on surfaces are unique, so that is narrower-acceptable. With that change the grade would be faithful.

### t99A01
- The whole statement is algebra:
  ```lean
  Nonempty (PresentedGroup (APMT99A01.rels {2}) ≃* Multiplicative (ZMod 2)) ∧ … Subsingleton (PresentedGroup (APMT99A01.rels {2, 4, 5})) ∧
  Nonempty (AddMonoidHom.ker APMT99A01.boundaryX ≃+ (Fin 0 → ℤ)) ∧ … ker boundaryY ≃+ ℤ ∧ … ker boundaryZ ≃+ (Fin 2 → ℤ)
  ```
  The values are correct: π₁ = Z/2, Z/2, 1 and H₂ = 0, ℤ, ℤ². H₁ = coker(·2), coker(2,4), coker(2,4,5) = Z/2, Z/2, 0 is omitted, even though it is algebraically trivial to add.
- A faithful version is expressible. Define X as the quotient of `Circle ⊕ closedBall` by z ↦ z^d on the boundary, then state `FundamentalGroup X x ≃* …` and `(singularHomologyFunctor (ModuleCat ℤ) n).obj (TopCat.of X) ≅ …`. The proof gap is van Kampen and cellular/Mayer–Vietoris homology. As it stands it is a stand-in, and none of the conjuncts involves a space.

### t99A02
- `(PresentedGroup.of (rels := rp2WedgeRp2Relations) 0) ^ 2 = 1` and its two siblings hold immediately because the relator is in the set, so they are near-vacuous. The only conjunct with content is `Infinite (PresentedGroup circleWedgeRp2Relations)`.
- π₁(RP²∨RP²) = D∞ is not even asserted to be infinite, and that infinitude is what makes the universal cover an infinite chain of spheres.
- "Sketch pictures" is not a proposition. The faithful content is ∃ a simply-connected `IsCoveringMap` from an explicit model. For RP²∨RP² that model is a ℤ-chain of S²'s; for S¹∨RP² it is a tree of lines and spheres. This is expressible with quotients plus `SimplyConnectedSpace`, but heavy. Minimum fix: `PresentedGroup rp2WedgeRp2Relations ≃* DihedralGroup 0` and `PresentedGroup circleWedgeRp2Relations ≃* Monoid.Coprod (Multiplicative ℤ) (Multiplicative (ZMod 2))`.

### t99A03
- The statement is:
  ```lean
  theorem apm_t99a03 {E B} … [ConnectedSpace E] (p : E → B) (hp : IsCoveringMap p) (τ : E ≃ₜ E) (hdeck : p ∘ τ = p) (hne : τ ≠ Homeomorph.refl E) : ∀ x : E, τ x ≠ x
  ```
  It is true by uniqueness of lifts on a connected E, but it is generic: no RP², no wedge, no #⁴RP². Both intended answers are correct. (a) Yes: the fourfold wedge is ℚ-acyclic, so L(f) = 1. (b) No: N₄ double-covers N₃, and the deck involution has no fixed points.
- Faithful version, expressible with what exists:
  - (b): `∃ f : C(ConstructionTargets.Surfaces.Surface false 4, _), ∀ x, f x ≠ x`.
  - (a): `∀ f : C(W, W), ∃ x, f x = x`, with W the quotient of `Σ i : Fin 4, RP²` (RP² = `Projectivization ℝ (Fin 3 → ℝ)` with the coinduced topology) gluing the basepoints.
  
  The proof gap for (a) is the Lefschetz theorem. (b) is provable from the deck lemma plus an explicit cover.

### t99A04
- The statement is:
  ```lean
  (hloop : g 1 = g 0) : (∫ x in (0 : ℝ)..1, deriv g x) = 0 ∧ ∀ c : ℝ, (∫ _x in (0 : ℝ)..1, c) = c
  ```
  It is true (FTC) and near-trivial, and it mentions no surface, embedding or form.
- The closedness of X repair is correct. The intended answers are: separating gives 0 (by Stokes on one side); nonseparating does not (torus, dx).
- Gap: Mathlib has `extDeriv` only on normed spaces. It has no differential forms on manifolds, no pullback or integration over a curve in a manifold, and no Stokes. A narrower faithful statement exists for (b) on `UnitAddCircle × UnitAddCircle`: η = a dx + b dy with ℤ²-periodic smooth a, b and closedness ∂a/∂y = ∂b/∂x; f is the x-loop; the period ∫₀¹ a(t,0) dt = 1 for η = dx, and the complement is connected. (a) in general needs the gap.

### t99J03
- The statement is:
  ```lean
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace apm_t99J03_E2 X] [IsManifold (𝓘(ℝ, apm_t99J03_E2)) ⊤ X],
    (∃! g : ℕ, Nonempty (X ≃ₜ apm_t99J03_Surface true g) ∧ …) ∨ (∃! k : ℕ, 0 < k ∧ Nonempty (X ≃ₜ apm_t99J03_Surface false k) ∧ …)
  ```
- **It is false.** `apm_t99J03_SurfaceRel true 0` requires `∃ j : ℕ, j < 0`, so it is empty, and `apm_t99J03_Surface true 0` ≃ₜ the closed unit disk. Take X = S² = `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`, which carries Mathlib's `IsManifold (𝓡 2) ω` instance and is compact, T2 and connected. S² is not homeomorphic to the disk. It is not homeomorphic to `Surface true g` for g ≥ 1 or to any `Surface false k` either, because those have χ ≤ 1 and are not simply connected. So both disjuncts fail.
- Fix (smallest): make genus 0 the sphere. Either add the word a a⁻¹ (a 2-gon with its two edges glued reversed) as the genus-0 case of `SurfaceRel`, or add a third disjunct `Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)` and restrict the orientable branch to 0 < g.
- The same `Surface true 0` = disk quirk is in `ConstructionTargets/Surfaces.lean` (shared, used by t98A01). It is harmless there, but any reuse for classification inherits the bug.
- Part (c) is vacuous: `apm_t99J03_eulerCharacteristic true g = 2 - 2 * g` is `rfl`. A faithful (c) is "same orientability and same χ ⇔ homeomorphic", with χ as an invariant (e.g. ranks of singular homology). That is expressible but heavy.
- Smooth instead of triangulated is narrower-acceptable. (b), "outline a proof", is not formalizable.

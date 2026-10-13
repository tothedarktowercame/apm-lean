# Statement fidelity triage, list 1

Read-only triage of `/home/joe/code/apm-lean/problems/<id>`. Sources read for each problem: problem.md, the `apm_<id>` theorem and the definitions it uses, PRELIM-DEFECT.md where one exists (only t00A04), and the STATEMENTS.json entry where one exists (only t00A04 and t01A08 are registered; none are revoked). No STATEMENT-REPAIR.md exists for any of these nine.

| id | class | grade-or-gap | one-line reason |
|---|---|---|---|
| t00A04 | D | repaired statement: faithful (stronger: orientation dropped) | As printed it is false when X is empty or a single point. The repair `[Nontrivial X]` is the smallest fix, and the repaired claim is true. |
| t01A05 | C | gap: no integration of top forms on manifolds (b) and no oriented intersection numbers or preimage submanifolds (c). The narrower homological stand-in for (b) is **FALSE as written** | (b) is replaced by π_*[X̃] = k[X] and (c) is dropped entirely. An orientation is defined as `H_n ≅ ℤ`, so it fails to exist for a disconnected X̃. Counterexample: the trivial 2-sheeted cover pt ⊔ pt → pt, or S¹ ⊔ S¹ → S¹. Fix: add `[ConnectedSpace Xtilde]`, or define orientation per component. |
| t01A08 | A | faithful (stronger) | Asks for a vertical line whose parameter p is a regular value of proj∘f, which implies f⁻¹(ℓ) is a submanifold. Second countability is needed and is added; the answer "yes" is committed. |
| t01J04 | B | the conclusion is too weak | `∃ charts : ChartedSpace … S` puts an arbitrary abstract smooth-with-boundary structure on the subspace f⁻¹(cl V), with no link to X's smooth structure. Fix: also require `Subtype.val` to be ContMDiff into X with injective mfderiv, which makes it an embedded submanifold with boundary. |
| t01J05 | B | **FALSE as written**, and adding `[T2Space X]` fixes it | `T2Space X` is missing. The circle with one point doubled is compact, boundaryless, smooth and 1-dimensional, and carries the nowhere-zero form dθ, but has H₀ = ℚ and H₁ = ℚ², so χ = −1. The orientation hypothesis is a pointwise choice and is vacuous, which is harmless. Part (a) is a definition (provided). |
| t01J06 | B | part (c) does not say ζ is closed | (a) and (b) are faithful through concrete encodings: an oriented coefficient against μH[2], with value 4π/3, and smooth ambient η with `extDeriv η = 0`. In (c), ζ is a pointwise family with no smoothness or closedness, so the clause holds by `rfl`. Fix: require ζ to be the restriction of a smooth form Z on an open W ⊇ S²×S¹ in E3×E2 with `extDeriv Z = 0` on W. A witness is pr₁*(ρ*α) with ρ(x) = x/\|x\|. |
| t02A08 | D | repaired statement: narrower-acceptable. Gap: intersection numbers are defined as deg(pr₂∘f) | {p}×S² and f(S²) are both 2-dimensional inside a 3-manifold, so the intersection number is undefined. The repair to Z = S¹×{q} is right. But `HasOrientedIntersection` is defined as a degree, so the "explain your computation" part holds by definition, and what is left is "every n is the degree of a map S²→S²". |
| t03J01 | D | repaired statement: faithful. Flag: the hypotheses carry part of the core | Cutting a genus-2 surface (χ = −2) along one curve cannot give a twice-punctured sphere (χ = 0). The repair to a twice-punctured torus is right, but `HasPrimitiveClass J₁` and `IsNullHomologous J₂` are supplied as hypotheses. The second is the key step of (b). Both follow from connectivity of the complement and should be dropped. |
| t03J04 | A | narrower-acceptable | The repairs n ≥ 1, X connected and T2 are all justified. Orientation is dropped, which makes the statement stronger. Part (b) proves χ(X) = 0 but never shows the value is attained (trivially X = Tⁿ). (a)(i) is just a pointwise nonzero function `Torus → E n`. The torus chart and manifold instances are bound as arguments, which only generalises the statement and is harmless. |

## Evidence notes

### t00A04 (D)
problem.md says only "X ⊂ Y smooth compact oriented manifolds without boundary". PRELIM-DEFECT.md observes that an empty or one-point X makes the claim false. The current Lean statement:
```lean
[T2Space X] [CompactSpace X] [Nontrivial X] ... [IsManifold I ∞ X] ...
∀ (ι : C(X, Y)) (r : C(Y, X)), ContMDiff I J ∞ ι → ContMDiff J I ∞ r →
  (∀ x, r (ι x) = x) → ¬ apm_t00a04_NullHomotopic ι
```
The model is `ModelWithCorners ℝ E E`. Its range is closed with nonempty interior and homeomorphic to E, so by invariance of domain it is all of E: the manifolds are effectively boundaryless. FiniteDimensional E is required. Orientation is dropped, which only strengthens the statement. The claim is true: if ι were null-homotopic, so would be id_X = r∘ι. A zero-dimensional X with at least two points is not path-connected, and a closed manifold of positive dimension is not contractible. Registry grade: "stronger". I agree. The superseded `apm_t00a04_previous_encoding`, which assumed id_X is not null-homotopic, is correctly retired.

### t01A05 (C, current statement false)
The module doc says "part (b) is replaced by its fundamental-class relation … Part (c) is explicitly deferred". The relevant definitions:
```lean
structure T01A05Orientation (n : ℕ) (X : Type) [TopologicalSpace X] where
  topIso : T01A05TopHomology n X ≅ ModuleCat.of ℤ ℤ
...
∀ (n k : ℕ) (hk : 0 < k) (X Xtilde : Type) ... [CompactSpace Xtilde] ...
  t01A05IsKSheetedCover k π →
  ∀ o : T01A05Orientation n X, ∃ ot : T01A05Orientation n Xtilde, ...
```
Nothing requires connectedness. Take n = 0, X = pt and X̃ = pt ⊔ pt with the fold map, k = 2. Then H₀(X) ≅ ℤ, so an o exists, but H₀(X̃) ≅ ℤ² ≇ ℤ, so no ot exists. The same happens with n = 1 and S¹ ⊔ S¹ → S¹. The prelim allows disconnected X̃, and the integral formula still holds there. Part (a) (`t01A05TorusCover k`, (x, y) ↦ (kx, y) on (ℝ/ℤ)², k > 0) is fine.

Gaps:
- (b) needs integration of n-forms on manifolds.
- (c) needs oriented intersection numbers and preimage submanifolds.

A narrower statement does exist: the fundamental-class relation with `[ConnectedSpace Xtilde]`, or with orientations defined per component. Note that the repair also changes "k for any k" to k > 0, which is fine.

### t01A08 (A, faithful/stronger)
```lean
[TopologicalSpace X] [SecondCountableTopology X] [ChartedSpace H X] [IsManifold I ⊤ X]
∃ p, ∀ x, f x ∈ apm_t01a08_line p →
  Function.Surjective (mfderiv I apm_t01a08_I2 (fun z => apm_t01a08_projection (f z)) x)
```
A regular value of π∘f gives a submanifold preimage, so this commits to the answer "yes", restricted to vertical lines, which is a stronger claim. It is true by Sard. When dim X < 2, the image of X has measure zero, so the existential is met by an empty preimage. The model I allows boundary, but Sard still applies. Registry grade: "stronger". I agree.

### t01J04 (B)
```lean
def apm_t01J04_IsSmoothManifoldWithBoundary (n : ℕ) (S : Type*) [TopologicalSpace S] : Prop :=
  (n = 0 ∧ ∃ charts : ChartedSpace (apm_t01J04_Euclidean n) S, ...) ∨
  (∃ hn : NeZero n, ∃ charts : ChartedSpace (EuclideanHalfSpace n) S, ...
      IsManifold (modelWithCornersEuclideanHalfSpace n) (⊤ : ℕ∞) S)
... apm_t01J04_IsSmoothManifoldWithBoundary n {x : X // x ∈ f ⁻¹' closure V}
```
The charts are existentially chosen and are not required to agree with X's atlas. That only says "the subspace is a topological n-manifold with boundary that admits some smooth structure". The prelim intends a smooth submanifold with boundary of X, namely the sublevel set {ρ∘f ≤ r} at a regular value r.

Smallest fix: inside the existential, also require that `Subtype.val` is `ContMDiff (half-space or self model) (model of X) ⊤` and has injective `mfderiv` at every point. Since the inclusion is already a closed topological embedding, this makes the subtype an embedded smooth submanifold with boundary.

The added T2/RegularSpace assumptions are justified (line with two origins). RegularSpace follows from T2 plus local compactness anyway.

### t01J05 (B, current statement false)
```lean
theorem apm_t01j05 (n : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (apm_t01J05_Euclidean n) X] [IsManifold (apm_t01J05_Model n) (⊤ : ℕ∞) X]
    [BoundarylessManifold (apm_t01J05_Model n) X] [CompactSpace X]
    (orientation : apm_t01J05_IsOrientation (n := n) X)
    (omega : apm_t01J05_OneForm (n := n) X) (homega_ne : ∀ x : X, omega x ≠ 0) :
    apm_t01J05_eulerCharacteristic n X = 0
```
There is no `T2Space X`. Counterexample: n = 1 and X = the circle with one point doubled, i.e. two copies of S¹ glued along S¹ minus a point. It is compact and smooth, its chart transitions are the identity, it is boundaryless, and dθ is a nowhere-zero smooth section. Mayer–Vietoris for the open cover by the two circle copies, which meet in an interval, gives H₀ = ℚ and H₁ = ℚ², so χ = 1 − 2 = −1. The sibling t03J04 cites this same counterexample when it adds `T2Space`.

`apm_t01J05_IsOrientation` is `Nonempty (∀ x, Orientation ℝ (TangentSpace …) (Fin n))`, which has no continuity condition and so always holds. That is harmless because the claim holds without orientability.

Fix: add `[T2Space X]`. Second countability then follows from compactness. With that, the statement is faithful, and proving it needs Poincaré–Hopf or the Euler class (a proof gap, not a statement gap). Part (a), `apm_t01J05_IsPartitionOfUnitySubordinate`, is a correct definition.

### t01J06 (B)
(a) and (b) are faithful.
- I checked the coefficient definition: Σ ±q_i α(P e_j, P e_k) recovers the coefficient of α against the outward area form.
- For ω = (z+3)dx∧dy that coefficient is (z+3)z, and its integral over S² is 4π/3, which matches the target.
- Nonexistence of η is stated as `¬ ∃ eta, ContDiff ℝ ⊤ eta ∧ extDeriv eta = 0 ∧ isInclusionPullback eta alpha`.

Part (c) is the problem:
```lean
abbrev apm_t01J06_ProductForm2 := ∀ qp : S2 × S1, (sphereTangent qp.1 × circleTangent qp.2) [⋀^Fin 2]→L[ℝ] ℝ
...
∀ p, ∃ zeta, zeta = apm_t01J06_projectionPullback alpha ∧ apm_t01J06_isJPullback p zeta alpha
```
This says nothing about ζ being closed, or even smooth, and it is already proved by `rfl` (`apm_t01J06_projectionPullback_isJPullback`). Mathlib has no d on manifolds, but closedness can still be stated ambiently: ∃ open W ⊇ S²×S¹ in E3×E2 and Z with ContDiffOn on W, `extDeriv Z = 0` on W, and ζ equal to Z restricted to tangent vectors. A witness exists: the pullback of α along (x, y) ↦ x/‖x‖ on (E3∖0)×E2. "Why is i*ω closed" is explanation only and needs no encoding.

### t02A08 (D)
problem.md: "Z = {p}×S² ⊂ Y = S¹×S² … f : S² → Y … I_X(f,Z) = n". Here dim f(S²) + dim Z = 4 ≠ 3 = dim Y, so I(f, Z) is undefined (the I_X typo aside). Lean repairs this to `apm_t02a08_Z q = {y | y.2 = q}`, i.e. S¹×{q}, and defines
```lean
def apm_t02a08_HasOrientedIntersection f Z n : Prop :=
  ∃ q, Z = apm_t02a08_Z q ∧ apm_t02a08_HasDegree (apm_t02a08_secondProjection.comp f) n
```
For this cycle, I(f, S¹×{q}) = deg(pr₂∘f) is mathematically correct. It is also exactly the computation the prelim asks to "explain in detail", and it is now true by definition (`apm_t02a08_fiberMap_hasOrientedIntersection` is already proved). What remains is "for every n there is g : S²→S² of degree n".

The gap is that Mathlib has no geometric oriented intersection numbers. The repaired statement is narrower-acceptable.

### t03J01 (D)
The module doc gives the χ argument: genus 2 has χ = −2, a twice-punctured sphere has χ = 0, and cutting along one curve does not change χ. So the prelim's J₁ cannot exist, and the repair to a twice-punctured torus follows the solution. The current definitions:
```lean
def apm_t03j01_CutsIntoTwicePuncturedTorus J := IsConnected (Jᶜ) ∧ apm_t03j01_HasPrimitiveClass J
def apm_t03j01_CutsIntoTwoOncePuncturedTori J := ¬IsConnected (Jᶜ) ∧ apm_t03j01_IsNullHomologous J
```
X is a compact, path-connected, T2 smooth surface with H₀ = ℤ, H₁ = ℤ⁴, H₂ = ℤ, so by classification it is the orientable genus-2 surface. Embedded circles in a surface are tame, so `Circle ≃ₜ J` is enough. The conclusion `RetractsOnto J₁ ∧ ¬RetractsOnto J₂` is true.

Flags:
- `IsNullHomologous J₂` is the key step of (b): a separating curve bounds, so H₁(J₂) → H₁(X) is zero. Giving it as a hypothesis reduces (b) to functoriality plus H₁(S¹) ≠ 0 (`apm_t03j01_no_retraction_of_curve_H1Map_zero`).
- `HasPrimitiveClass J₁` likewise supplies the dual class used in (a).

Both are consequences of the connectivity conditions and should be dropped. The conclusion stays true without them, including when J₂ bounds a disc.

### t03J04 (A, narrower-acceptable)
```lean
theorem apm_t03j04 (n : ℕ) [NeZero n]
    [ChartedSpace (apm_t03J04_HModel n) (apm_t03J04_Torus n)]
    [IsManifold (apm_t03J04_Model n) (⊤ : ℕ∞) (apm_t03J04_Torus n)] :
    (∀ q, apm_t03J04_constantVectorField n q ≠ 0) ∧
    apm_t03J04_eulerCharacteristic n (apm_t03J04_Torus n) = 0 ∧
    ∀ (X : Type) ... [T2Space X] ... [BoundarylessManifold ...] [ConnectedSpace X] (phi : Torus n → X),
      IsLocalDiffeomorph ... phi → apm_t03J04_eulerCharacteristic n X = 0
```
The repairs (n ≥ 1, X connected, X Hausdorff) are documented and justified. Dropping orientation-preserving only strengthens the statement. The claim is true: φ is a finite covering onto a compact X, so 0 = χ(Tⁿ) = d·χ(X). This holds for whatever chart instance on the torus is passed in, since the topology is the Pi topology.

Shortfalls:
- "List all possible values" is answered only by the bound χ = 0, not by showing 0 is realised. The witness X = Tⁿ, φ = id is trivial.
- (a)(i) is a nonzero function into `E n` (which is TangentSpace by definition). No smoothness is required, which is acceptable for an "explicit example".

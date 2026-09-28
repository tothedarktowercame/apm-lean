# Re-open fidelity grades, batch 1 (current `theorem apm_<id>` only)

Graded read-only against `problems/<id>/problem.md` in /home/joe/code/apm-lean, 2026-09-28.
`apm_<id>_previous_encoding` was ignored. Smoothness check: in the pinned Mathlib,
`.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:112-114` defines
`ω := (⊤ : WithTop ℕ∞)` and `∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)`. Only t94J08 has a smoothness order, and it uses bare `⊤`, which means analytic.

| id | grade | decl | one-line reason | prelim-defect? |
|---|---|---|---|---|
| t00A01 | false | `apm_t00a01` | `φᵢ` only has to be injective, not continuous, and `Mᵢ` is any space with S³ homology rather than a manifold. A bijection `D³ → S³` sending `S²` onto a circle makes X a circle, so π₁ = ℤ ≠ 1 * 1 and H₁ ≠ 0 | no |
| t00J06 | stronger, truth not established (suspected false) | `apm_t00j06` | The genus-2 surface is replaced by any compact T2 path-connected space with genus-2 singular homology, with no manifold or local path-connectedness hypothesis. The covering-space argument does not apply in that generality | no |
| t02A01 | false | `apm_t02a01` | Nothing makes `S` a punctured torus or `boundary` its boundary. The double cover `z ↦ z²` of S¹ with `boundary = univ` gives 1 component, not 2 | no |
| t91A01 | false | `apm_t91a01` | In (b), `F` is any compact connected space, `V` is any continuous map to a normed space, and the index-3 hypothesis `∃ link, link z = z^3` is always true and never mentions `V`. Counterexample: `F` a point, `V = 0` | no |
| t94J08 | narrower | `apm_t94j08` | `hv : ContDiff ℝ ⊤ v` restricts (b) to analytic fields. The n = 0 case of (a) is replaced by a `Fin 2` swap fact with no degree in it. The m = 0 (1-dimensional) case of (b) is vacuous because `H₀(S⁰) ≇ ℤ` | partial: the n = 0 degree needs reduced homology (S⁰ ambiguity), but nothing in the prelim forces `⊤` |
| t96J07 | narrower | `apm_t96j07` | The fixed points and the continuous `f` are genuine. The local indices are a `def` evaluated from a hand-supplied `det(I - diag)` formula that never mentions `f`, and `L(f)` is reduced to `f_* = id` on H₀ and H₃ plus the literal `(1:ℤ) - 1 = 0` | no |

## Evidence

### t00A01
The current statement's hypotheses:
```lean
(φ₁ : apm_t00A01_Disk3 → M₁) (φ₂ : apm_t00A01_Disk3 → M₂)
(hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
(hM₁ : apm_t00A01_isHomology3Sphere M₁)
(hM₂ : apm_t00A01_isHomology3Sphere M₂) :
```
`M₁ M₂ : Type` have only `[TopologicalSpace]` and the singular-homology condition `H₀ ≅ ℤ, H₃ ≅ ℤ, other Hₖ = 0`. The statement has no manifold, closedness or triangulation hypothesis, and `φᵢ` need not be continuous.
`apm_t00A01_punctured φ` is the subtype `{x // x ∉ φ '' {|y| < 1}}`.

**Counterexample.** Take M₁ = M₂ = S³ and φ₁ = φ₂ = φ, where φ is a set bijection `D³ → S³` that maps `S²` bijectively onto a great circle C. The cardinalities match, and φ is injective but not continuous. Then:
- the punctured piece is C with its subspace topology, a circle;
- `boundaryMap` is a bijection from `S²` onto C;
- the gluing identifies each point of the left copy of C with the same point of the right copy, so X is homeomorphic to C (the fold map is a quotient map).

So π₁(X) ≅ ℤ, while `Monoid.Coprod 1 1` is trivial, and H₁(X) ≅ ℤ ≠ 0. Both conjuncts fail.

Requiring φ to be continuous would not be enough, because the statement also needs a manifold hypothesis. For example, take S³ with an arc attached at one point. It has S³ homology. If the attachment point lies inside φ(open ball), the whisker becomes a separate component of the punctured piece, so H₀(X) ≅ ℤ².

The conclusion itself is a reasonable encoding: `π₁(X) ≅ π₁M₁ * π₁M₂`, and X is an integral homology 3-sphere.

### t00J06
```lean
theorem apm_t00j06
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [PathConnectedSpace S]
    (hS : apm_t00J06_hasGenusTwoHomology S)
    (f : C(apm_t00J06_Torus, S)) :
    ∃ (X : Type*) (_ : TopologicalSpace X) (_ : ConnectedSpace X) (p : X → S),
      IsCoveringMap p ∧ (∀ s : S, (p ⁻¹' ({s} : Set S)).Infinite) ∧
      ∃ lift : C(apm_t00J06_Torus, X), ∀ x, p (lift x) = f x
```
The conclusion is good: a connected covering with infinite fibres, a real `IsCoveringMap`, and a continuous lift. The repaired previous encoding had a disconnected cover, and that defect is now fixed.

The hypothesis is the problem. `hasGenusTwoHomology` only states singular homology ℤ, ℤ⁴, ℤ, 0. The previous encoding's `ChartedSpace`/`IsManifold` instances have been dropped. The prelim's surface satisfies these hypotheses, so the Lean statement implies the prelim claim, which makes it stronger.

Its truth is not established. The informal proof uses covering-space classification, which needs a locally path-connected, semilocally simply connected base. For a compact Hausdorff space whose covers see Čech-type loops rather than singular loops, this can break. Suspected counterexample: attach Warsaw-circle-bounded disks to Σ₂ so that a₁, b₁ and a₂ become Čech-null while staying singularly essential. Then every covering of S has monodromy factoring through ⟨b₂⟩. For `f` through b₂, a lift then forces a trivial connected cover. I have not verified that this S keeps the singular homology exactly, so this is a suspicion, not a refutation.

Recommendation: restore a surface hypothesis (for example the previous `ChartedSpace`/`IsManifold`, or at least local path-connectedness plus semilocal simple connectivity). Then the statement is faithful.

### t02A01
```lean
theorem apm_t02a01
    {S Stilde : Type*} [TopologicalSpace S] [TopologicalSpace Stilde]
    (boundary : Set S) (p : Stilde → S) (n : ℕ) (hn : 0 < n)
    (hboundary : Nat.card (ConnectedComponents boundary) = 1)
    (hcover : IsCoveringMap p)
    (hregularCyclic : ∃ deck : ZMod n → Homeomorph Stilde Stilde,
      (∀ z x, p (deck z x) = p x) ∧
      (∀ x y, p x = p y → ∃! z, deck z x = y)) :
    Nat.card (ConnectedComponents (p ⁻¹' boundary)) = n
```
Nothing says S is a torus minus a disk, and nothing says `boundary` is its boundary circle. Only "`boundary` is connected" is assumed.

**Counterexample.** Take n = 2, S = S̃ = S¹, p(z) = z², deck transformations z ↦ ±z (simply transitive on fibres), and boundary = univ. Then p⁻¹(boundary) = S¹ has 1 component, not 2.

The statement is false even for the correct S if `boundary` is taken to be a non-separating loop that is unwrapped by the cover. `deck` is also not required to be a group homomorphism, but that is minor next to the missing S.

### t91A01
```lean
∀ (F : Type*) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace F] [CompactSpace F] [ConnectedSpace F]
  (V : F → E) (p : F),
  Continuous V → V p = 0 →
  (∃ U ∈ nhds p, ∀ q ∈ U, V q = 0 → q = p) →
  (∃ link : C(Circle, Circle), ∀ z : Circle, link z = z ^ 3) →
  ∃ q : F, q ≠ p ∧ V q = 0
```
The "zero as in part (a)" hypothesis is a closed proposition, always inhabited by `z ↦ z^3`, and it does not mention `V` or `p`. The statement has no surface, no tangent bundle, no orientation and no smoothness.

**Counterexamples:**
- F = PUnit, E = ℝ, V = 0. The zero is isolated (U = univ), and no q ≠ p exists.
- On a genuine surface: F = S², E = ℝ³, V a tangent field with a single zero of index 2. The Lean statement still demands a second zero.

Part (a), the `z ↦ z³` model with winding `exp(3iθ)`, is an acceptable encoding of "draw an index-3 zero".

### t94J08
```lean
(∀ n : ℕ, 1 ≤ n → t94J08HasDegree n t94J08Antipodal ((-1 : ℤ) ^ (n + 1))) ∧
∀ (m : ℕ) (v : ...) (hv : ContDiff ℝ ⊤ v) (p : ...) (hp : t94J08HasIsolatedZero v p)
  (r : ℝ) (hr : 0 < r) (hlink ...) (hlinkNeg ...) (d : ℤ),
  t94J08HasLocalIndex v p r hlink d →
  t94J08HasLocalIndex (fun x ↦ -v x) p r hlinkNeg ((-1 : ℤ) ^ (m + 1) * d)
```
Degree is taken on the actual integral top singular homology, and the answer (-1)^(n+1) is correct for n ≥ 1. Part (b) has the right answer, (-1)^dim · d, and working in a local chart ℝ^(m+1) is a reasonable encoding.

What is dropped:
1. **`hv : ContDiff ℝ ⊤ v` means analytic (C^ω), not C^∞.** The prelim says "vector field", so smooth or even continuous fields are covered there. Since `hv` is not needed for the conclusion, this is a gratuitous restriction. Use `∞`, or drop `hv`.
2. **The n = 0 case of (a)** is replaced by `(Equiv.swap 0 1) 0 = 1 ∧ (Equiv.swap 0 1) 1 = 0` on `Fin 2`. This holds by `rfl` and states no degree, so the S⁰ case is not represented.
3. **The m = 0 case of (b)** (a 1-dimensional manifold) is quantified but vacuous. `t94J08HasLocalIndex` for m = 0 asks for `H₀(S⁰) ≅ ℤ`, which is false, so the premise can never hold.

On the prelim: whether "degree" makes sense on S⁰ is ambiguous and needs reduced homology. That partly excuses items 2 and 3, but not item 1.

### t96J07
```lean
∃ f : C(apm_t96j07_RP3, apm_t96j07_RP3),
  (∀ x hx, f (mk x) = mk (A x)) ∧
  (∀ q, f q = q ↔ ∃ i, q = mk (axis i)) ∧
  apm_t96j07_localIndex 0 = -1 ∧ ... ∧ apm_t96j07_localIndex 3 = 1 ∧
  (∑ i, apm_t96j07_localIndex i) = 0 ∧
  apm_t96j07_Hmap 0 f = 𝟙 _ ∧ apm_t96j07_Hmap 3 f = 𝟙 _ ∧
  ((1 : ℤ) - 1) = 0
```
with
```lean
def apm_t96j07_localDeterminant (i : Fin 4) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (1 - (j.val + 1 : ℝ) / (i.val + 1 : ℝ))
def apm_t96j07_localIndex (i : Fin 4) : ℤ := if 0 < apm_t96j07_localDeterminant i then 1 else -1
```

**What is genuine.** The continuous map on the quotient-topology RP³ agrees with `[x₀, 2x₁, 3x₂, 4x₃]`, and the fixed points are exactly the four coordinate axes. `f_* = id` on the actual integral H₀ and H₃ is also real content, and true: f is homotopic to the identity through positive diagonal matrices.

**What is decoupled from f:**
- The local Lefschetz numbers are a closed arithmetic `def` that never mentions `f`, its derivative or any fixed-point index. The formula is sign det(I − Df) in the chart x_i = 1, and the values -1, 1, -1, 1 are correct. But computing them is arithmetic on a formula the statement supplies. STATEMENT-REPAIR.md says as much: "it adds no theorem comparing these definitions with an intrinsic projective derivative."
- The global Lefschetz number L(f) = Σ(-1)^k tr(f_* | H_k(ℚ)) is not defined. It is replaced by the two identity facts plus the literal `(1:ℤ) - 1 = 0`. H₁ = ℤ/2 and H₂ = 0 are never stated to contribute nothing.

The statement is narrower: the local-index and L(f) parts are not tied to f. The prelim is not defective.

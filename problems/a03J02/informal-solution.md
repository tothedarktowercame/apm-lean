# APM a03J02: Polynomial maps send null sets to null sets (Lusin's condition N)

## Why It's Hard

A generic continuous map can blow up null sets to positive measure — space-filling curves are the classic example. Even smooth maps can fail: a $C^{n-1}$ map $\mathbb{R}^{n} \to \mathbb{R}^{n}$ might not preserve null sets. The result requires something special about polynomial maps. The key is that polynomial maps are **locally Lipschitz**, and Lipschitz maps preserve null sets. But "locally Lipschitz" isn't quite enough on all of $\mathbb{R}^{n}$ (the Lipschitz constant grows), so you need to combine local Lipschitz control with a covering argument that respects the polynomial growth.

## The Key Insight

**Lipschitz maps preserve null sets** (they distort volumes by at most $L^n$ on each ball). A polynomial map $f$ is smooth, hence locally Lipschitz: on any bounded set, $\|Df\|$ is bounded (since the entries of the Jacobian are polynomials, hence bounded on bounded sets). Cover $E$ by balls of total measure $< \varepsilon$, control the Lipschitz constant on each ball, and conclude $m(f(E)) < C \cdot \varepsilon$.

More precisely: partition $\mathbb{R}^{n}$ into cubes $Q_k$ of side 1. On each $Q_k$, the derivative $Df$ is bounded by some $L_k$. Then $f$ maps null subsets of $Q_k$ to null sets (with dilation factor $L_k^n$). Since $E = \cup(E \cap Q_k)$ and each $f(E \cap Q_k)$ is null, $f(E)$ is null (countable union of null sets).

## Complete Proof

**Theorem.** Let $f : \mathbb{R}^{n} \to \mathbb{R}^{n}$ be a polynomial map. If $E \subset \mathbb{R}^{n}$ has Lebesgue measure zero, then $f(E)$ has Lebesgue measure zero.

**Proof.**

**Step 1: Locally Lipschitz property.**

Since each component $f_{i}$ is a polynomial, the partial derivatives $\partial f_{i}/\partial x_{j}$ are also polynomials. On any bounded set $B \subset \mathbb{R}^{n}$, each partial derivative is bounded:

$$\sup_{x \in B}\left|\frac{\partial f_i}{\partial x_j}(x)\right| \leq C_B < \infty.$$

By the mean value inequality (for vector-valued functions), for any $x, y$ in a convex bounded set $B$:

$$|f(x) - f(y)| \leq L_B \cdot |x - y|$$

where $L_B = n \cdot \max_{i,j} \sup_B |\partial f_{i}/\partial x_{j}|$ (or $L_B = \sup_B \|Df\|_{op}$, the operator norm of the Jacobian).

**Step 2: Lipschitz maps send null sets to null sets.**

**Lemma.** If $g : \mathbb{R}^{n} \to \mathbb{R}^{n}$ is Lipschitz with constant $L$ on a set $S$, and $m(S) = 0$, then $m(g(S)) = 0$.

*Proof of lemma.* Fix $\varepsilon > 0$. Since $m(S) = 0$, cover $S$ by countably many balls $B(x_{i}, r_{i})$ with $\sum r_{i}^{n} < \varepsilon$ (we can use balls of volume $< \varepsilon$). Then $g(S \cap B(x_{i}, r_{i})) \subset B(g(x_{i}), Lr_{i})$ (since $g$ is $L$-Lipschitz on $S$). So:

$$m(g(S)) \leq \sum_i m(B(g(x_i), Lr_i)) = \sum_i \omega_n (Lr_i)^n = L^n \omega_n \sum_i r_i^n < L^n \omega_n \varepsilon.$$

Since $\varepsilon > 0$ was arbitrary, $m(g(S)) = 0$. ∎

**Step 3: Decompose into bounded pieces.**

Partition $\mathbb{R}^{n}$ into the unit cubes $Q_k = [k_{1}, k_{1}+1) \times \cdots \times [k_{n}, k_{n}+1)$ for $k = (k_{1},\ldots,k_{n}) \in \mathbb{Z}^{n}$. These are countably many, pairwise disjoint, and $\cup Q_k = \mathbb{R}^{n}$.

Set $E_k = E \cap Q_k$. Then $E = \cup_k E_k$ (disjoint), and each $E_k \subset Q_k$ is contained in a bounded convex set.

**Step 4: $f$ is Lipschitz on each $Q_k$.**

On the bounded convex set $Q_k$, the Jacobian $Df$ is bounded (polynomial entries on a bounded set). Let $L_k = \sup_{x \in Q_k} \|Df(x)\|_{op}$. Then $f$ is $L_k$-Lipschitz on $Q_k$ (by the mean value theorem for Lipschitz estimates on convex sets).

**Step 5: Each $f(E_k)$ is null.**

Since $m(E) = 0$ and $E_k \subset E$, we have $m(E_k) = 0$. By Step 2 (the lemma), since $f$ is $L_k$-Lipschitz on $Q_k \supset E_k$, $m(f(E_k)) = 0$.

**Step 6: $f(E)$ is null.**

$$f(E) = f\left(\bigcup_k E_k\right) = \bigcup_k f(E_k).$$

This is a countable union of null sets, hence null. ∎

**Remark.** The proof uses only that $f$ is $C^{1}$ (so that $Df$ exists and is continuous, hence locally bounded). The polynomial hypothesis is stronger than needed — the result holds for any $C^{1}$ map $\mathbb{R}^{n} \to \mathbb{R}^{n}$. (For $C^{1}$ maps, local Lipschitz follows from continuity of the derivative.) The result even holds for locally Lipschitz maps, which includes all $C^{1}$ maps.

## What Connects

**To Sard's theorem.** Sard's theorem says: the set of *critical values* of a $C^k$ map ($k$ large enough) has measure zero. This problem is different — it says the *image of any null set* has measure zero, without restriction to critical points. This is Lusin's condition (N), and it holds for all $C^{1}$ maps (not just polynomial ones).

**To the change of variables formula.** The change of variables theorem says $\int_{f(E)} g = \int_E (g \circ f)|\det Df|$. If $m(E) = 0$, then $\int_E$ anything $= 0$, consistent with $m(f(E)) = 0$. But the change of variables formula requires $f$ to be injective (or uses multiplicity), while Lusin's condition (N) holds without injectivity.

**To the area formula.** The area formula (Federer) generalises the change of variables: $m(f(E)) \leq \int_E |\det Df| dx$ (with equality when $f$ is injective). Since $m(E) = 0$, the right side is 0, giving $m(f(E)) = 0$. This is the "sophisticated" proof; our proof via Lipschitz control is more elementary.

**To the Jacobian conjecture.** For polynomial maps $f : \mathbb{C}^{n} \to \mathbb{C}^{n}$, the Jacobian conjecture asks: if $\det(Df)$ is a nonzero constant, is $f$ a bijection? The measure-theoretic property (null sets map to null sets) is a much weaker consequence of polynomial structure, and holds without any hypothesis on the Jacobian.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Metric Set

noncomputable section

variable {n : ℕ}

/-- A polynomial map ℝⁿ → ℝⁿ (each component is polynomial). -/
def IsPolynomialMap (f : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ i : Fin n, ∃ p : MvPolynomial (Fin n) ℝ,
    ∀ x, f x i = MvPolynomial.eval x p

/-- Polynomial maps are smooth (C^∞). -/
lemma isPolynomialMap_contDiff {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : IsPolynomialMap f) :
    ContDiff ℝ ⊤ f := by
  sorry

/-- Lipschitz maps send null sets to null sets. -/
lemma measure_image_eq_zero_of_lipschitzOn
    {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {S : Set (Fin n → ℝ)} {L : ℝ≥0}
    (hlip : LipschitzOnWith L f S)
    (hS : volume S = 0) :
    volume (f '' S) = 0 := by
  sorry

/-- A C¹ map is Lipschitz on any bounded convex set. -/
lemma lipschitzOn_of_contDiffOn_bounded
    {f : (Fin n → ℝ) → (Fin n → ℝ)}
    (hf : ContDiff ℝ 1 f)
    {S : Set (Fin n → ℝ)} (hS : Bornology.IsBounded S) (hSc : Convex ℝ S) :
    ∃ L : ℝ≥0, LipschitzOnWith L f S := by
  sorry

/-- The unit cube decomposition: ℝⁿ = ⊔_k Q_k where each Q_k is bounded. -/
lemma exists_countable_cover_bounded :
    ∃ (Q : ℤ ^ n → Set (Fin n → ℝ)),
      (∀ k, Bornology.IsBounded (Q k)) ∧
      (∀ k, Convex ℝ (Q k)) ∧
      (∀ k, MeasurableSet (Q k)) ∧
      Pairwise (Disjoint on Q) ∧
      (⋃ k, Q k) = Set.univ := by
  sorry

/-- Countable union of null sets is null. -/
lemma measure_iUnion_null {ι : Type*} [Countable ι]
    {S : ι → Set (Fin n → ℝ)} (hS : ∀ i, volume (S i) = 0) :
    volume (⋃ i, S i) = 0 := by
  sorry

/-- Main theorem: polynomial maps send null sets to null sets. -/
theorem polynomial_map_image_null
    {f : (Fin n → ℝ) → (Fin n → ℝ)} (hf : IsPolynomialMap f)
    {E : Set (Fin n → ℝ)} (hE : volume E = 0) :
    volume (f '' E) = 0 := by
  sorry

/-- More general version: C¹ maps send null sets to null sets
    (Lusin's condition N). -/
theorem contDiff_map_image_null
    {f : (Fin n → ℝ) → (Fin n → ℝ)} (hf : ContDiff ℝ 1 f)
    {E : Set (Fin n → ℝ)} (hE : volume E = 0) :
    volume (f '' E) = 0 := by
  sorry

/-- The image of a null subset of a bounded set under a Lipschitz map
    is null — the key local step. -/
lemma image_null_of_lipschitzOn_null
    {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {Q : Set (Fin n → ℝ)} {L : ℝ≥0}
    (hlip : LipschitzOnWith L f Q)
    {E : Set (Fin n → ℝ)} (hEQ : E ⊆ Q) (hE : volume E = 0) :
    volume (f '' E) = 0 := by
  sorry

end
```

**Mathlib notes:**

- `IsPolynomialMap f` says each component `f x i` is the evaluation of a multivariate polynomial `MvPolynomial (Fin n) ℝ` at $x$. This is the natural Mathlib encoding.
- `LipschitzOnWith L f S` says $f$ is $L$-Lipschitz on $S$: `∀ x ∈ S, ∀ y ∈ S, dist (f x) (f y) ≤ L * dist x y`.
- `ContDiff ℝ 1 f` says $f$ is $C^{1}$ (continuously differentiable). The lemma `lipschitzOn_of_contDiffOn_bounded` extracts a Lipschitz constant on bounded convex sets.
- `volume (f '' E) = 0` uses the image `f '' E` and Lebesgue outer measure (which equals the measure for measurable sets, and provides an upper bound in general).
- The proof chains: `isPolynomialMap_contDiff` (polynomial ⟹ smooth) → `lipschitzOn_of_contDiffOn_bounded` ($C^{1}$ + bounded ⟹ Lipschitz) → `image_null_of_lipschitzOn_null` (Lipschitz + null ⟹ null image) → `exists_countable_cover_bounded` (decompose $\mathbb{R}^{n}$) → `measure_iUnion_null` (countable union of null is null).
- The more general `contDiff_map_image_null` states the result for all $C^{1}$ maps, not just polynomial ones — polynomial is stronger than needed.

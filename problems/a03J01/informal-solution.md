

# APM a03J01: Counting multiplicity in overlapping measurable sets

## Why It's Hard

The sets F\_j partition ℝⁿ (modulo the set of points in no E\_k) by multiplicity of membership. The identity A = Σ j·m(F\_j) says that the total measure, counted with overlaps, equals the sum weighted by multiplicity. This is intuitive — each "layer" of overlap is counted exactly as many times as it should be — but making it rigorous requires connecting the sum of measures Σ m(E\_k) to an integral of a counting function, then decomposing that integral by level sets. The key difficulty is justifying the interchange of summation and integration for a potentially uncountable collection of overlapping sets.

## The Key Insight

Define the **counting function** N(x) = #{k : x ∈ E\_k} = Σ\_k 1\_{E\_k}(x). Then:

- Σ m(E\_k) = Σ ∫ 1\_{E\_k} = ∫ Σ 1\_{E\_k} = ∫ N(x) dx (by Tonelli, since all terms are nonneg).
- F\_j = {x : N(x) = j}, and the F\_j partition the space (up to the set where N = 0).
- ∫ N(x) dx = ∫ Σ\_j j · 1\_{F\_j}(x) dx = Σ\_j j · m(F\_j) (by Tonelli again).

Both equalities use the monotone convergence theorem / Tonelli for nonneg functions and the level-set decomposition N = Σ j · 1\_{F\_j}.

## Complete Proof

**Theorem.** Let {E\_k} be Lebesgue measurable sets in ℝⁿ with A = Σ m(E\_k) < ∞. Let F\_j = {x ∈ ℝⁿ : x belongs to precisely j of the sets E\_k}. Then A = Σ\_{j=1}^∞ j · m(F\_j).

**Proof.**

**Step 1: Define the counting function.**

$$N(x) = \sum_{k=1}^{\infty}\mathbf{1}_{E_k}(x) = \#\{k : x \in E_k\}.$$

Each 1\_{E\_k} is measurable, so N is measurable (as a countable sum of measurable functions). N takes values in {0, 1, 2, ...} ∪ {∞}.

**Step 2: Σ m(E\_k) = ∫ N(x) dx.**

By the monotone convergence theorem (Tonelli's theorem for nonneg functions):

$$\sum_{k=1}^{\infty}m(E_k) = \sum_{k=1}^{\infty}\int_{\mathbb{R}^n}\mathbf{1}_{E_k}(x)\,dx = \int_{\mathbb{R}^n}\sum_{k=1}^{\infty}\mathbf{1}_{E_k}(x)\,dx = \int_{\mathbb{R}^n}N(x)\,dx.$$

So A = ∫ N(x) dx. Since A < ∞, N is finite a.e. (N(x) < ∞ for a.e. x). ✓

**Step 3: Level set decomposition.**

The sets F\_j = {x : N(x) = j} = N⁻¹({j}) are measurable and pairwise disjoint. Define F\_0 = {x : N(x) = 0} (the set of points in none of the E\_k). Then:

$$\mathbb{R}^n = F_0 \cup F_1 \cup F_2 \cup \cdots$$

(disjoint union, up to a null set where N = ∞, which has measure zero since A < ∞).

On F\_j, N(x) = j. So:

$$N(x) = \sum_{j=0}^{\infty} j \cdot \mathbf{1}_{F_j}(x)$$

(the j = 0 term contributes nothing).

**Step 4: Integrate by level sets.**

$$\int_{\mathbb{R}^n} N(x)\,dx = \int_{\mathbb{R}^n}\sum_{j=1}^{\infty} j \cdot \mathbf{1}_{F_j}(x)\,dx = \sum_{j=1}^{\infty} j \int_{\mathbb{R}^n}\mathbf{1}_{F_j}(x)\,dx = \sum_{j=1}^{\infty} j \cdot m(F_j).$$

The interchange of sum and integral is justified by the monotone convergence theorem (all terms are nonneg).

**Step 5: Combine.**

$$A = \sum_{k=1}^{\infty}m(E_k) = \int N(x)\,dx = \sum_{j=1}^{\infty}j\cdot m(F_j). \qquad \blacksquare$$

## What Connects

**To the layer cake / Cavalieri principle.** The identity ∫ N = Σ j · m(F\_j) is the discrete version of the layer cake formula ∫ f = ∫₀^∞ m({f > t}) dt. Here N is integer-valued, so the integral over heights becomes a sum over levels.

**To the inclusion-exclusion principle.** The counting function N(x) is the "multiplicity" version of inclusion-exclusion. The sets F\_j decompose the space by multiplicity, and the identity A = Σ j·m(F\_j) is the measure-theoretic analogue of the combinatorial identity Σ|A\_k| = Σ j·|F\_j| for finite sets.

**To the Borel-Cantelli lemma.** The hypothesis A = Σ m(E\_k) < ∞ implies (by Borel-Cantelli) that m(lim sup E\_k) = 0 — a.e. x belongs to only finitely many E\_k. This is why N(x) < ∞ a.e. and the F\_j partition is well-defined (modulo a null set).

**To probability.** If the E\_k are events in a probability space, then A = Σ P(E\_k) = E[N], the expected number of events that occur. The identity E[N] = Σ j·P(F\_j) is just computing the expectation of N via its probability mass function. This is sometimes called the "counting lemma" or "multiplicity formula."

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory Set Filter ENNReal

noncomputable section

variable {n : ℕ}

/-- The counting function N(x) = #{k : x ∈ E_k} = Σ 𝟙_{E_k}(x). -/
def countingFn (E : ℕ → Set (Fin n → ℝ)) (x : Fin n → ℝ) : ℕ∞ :=
  ∑' k, (E k).indicator (fun _ => (1 : ℕ∞)) x

/-- More usable ℝ≥0∞-valued counting function. -/
def countingFnENNReal (E : ℕ → Set (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ∑' k, (E k).indicator (fun _ => (1 : ℝ≥0∞)) x

/-- The multiplicity level set: F_j = {x : N(x) = j}. -/
def levelSet (E : ℕ → Set (Fin n → ℝ)) (j : ℕ) : Set (Fin n → ℝ) :=
  {x | (Finset.univ.filter (fun k => x ∈ E k)).card = j}

/-- Step 1: Σ m(E_k) = ∫ N(x) dx (Tonelli). -/
theorem sum_measure_eq_lintegral_counting
    {E : ℕ → Set (Fin n → ℝ)} (hE : ∀ k, MeasurableSet (E k)) :
    ∑' k, volume (E k) =
      ∫⁻ x, countingFnENNReal E x ∂volume := by
  sorry

/-- Step 2: N(x) < ∞ a.e. when Σ m(E_k) < ∞ (Borel-Cantelli). -/
lemma countingFn_ae_finite
    {E : ℕ → Set (Fin n → ℝ)} (hE : ∀ k, MeasurableSet (E k))
    (hA : ∑' k, volume (E k) ≠ ⊤) :
    ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
      countingFnENNReal E x ≠ ⊤ := by
  sorry

/-- Step 3: The level sets are measurable. -/
lemma levelSet_measurable
    {E : ℕ → Set (Fin n → ℝ)} (hE : ∀ k, MeasurableSet (E k))
    (j : ℕ) :
    MeasurableSet (levelSet E j) := by
  sorry

/-- Step 4: The level sets partition ℝⁿ (up to the null set {N = ∞}). -/
lemma levelSet_pairwise_disjoint
    {E : ℕ → Set (Fin n → ℝ)} :
    Pairwise (Disjoint on levelSet E) := by
  sorry

/-- Step 5: N(x) = Σ_j j · 𝟙_{F_j}(x) (level set decomposition). -/
lemma countingFn_eq_sum_levelSet
    {E : ℕ → Set (Fin n → ℝ)}
    {x : Fin n → ℝ} (hx : countingFnENNReal E x ≠ ⊤) :
    countingFnENNReal E x =
      ∑' j, (j : ℝ≥0∞) * (levelSet E j).indicator (fun _ => 1) x := by
  sorry

/-- Step 6: ∫ N dx = Σ j · m(F_j) (Tonelli on the level set decomposition). -/
theorem lintegral_counting_eq_sum_levelSet
    {E : ℕ → Set (Fin n → ℝ)} (hE : ∀ k, MeasurableSet (E k))
    (hA : ∑' k, volume (E k) ≠ ⊤) :
    ∫⁻ x, countingFnENNReal E x ∂volume =
      ∑' j, (j : ℝ≥0∞) * volume (levelSet E j) := by
  sorry

/-- Main theorem: A = Σ_{j≥1} j · m(F_j). -/
theorem sum_measure_eq_weighted_levelSet_sum
    {E : ℕ → Set (Fin n → ℝ)} (hE : ∀ k, MeasurableSet (E k))
    (hA : ∑' k, volume (E k) ≠ ⊤) :
    ∑' k, volume (E k) =
      ∑' j, ((j : ℕ) + 1 : ℝ≥0∞) * volume (levelSet E (j + 1)) := by
  sorry

/-- Alternative statement with the sum starting at j = 1. -/
theorem sum_measure_eq_weighted_levelSet_sum'
    {E : ℕ → Set (Fin n → ℝ)} (hE : ∀ k, MeasurableSet (E k))
    (hA : ∑' k, volume (E k) ≠ ⊤) :
    ∑' k, volume (E k) =
      ∑' j, (j : ℝ≥0∞) * volume (levelSet E j) := by
  sorry

end
```

**Mathlib notes:**

- `countingFnENNReal E x = ∑' k, (E k).indicator (fun _ => 1) x` is the counting function N(x) valued in ℝ≥0∞ — the tsum of indicators.
- `levelSet E j` is defined using `Finset.filter` on a universal finset — but for an infinite index, this needs care. In practice, for a.e. x (where N(x) < ∞), the number of k with x ∈ E\_k is finite, and `levelSet E j` is the set where exactly j indicators are 1. The measurability follows from countable operations.
- `∑' k, volume (E k)` is the tsum in ℝ≥0∞ (always well-defined, possibly ⊤).
- The main identity `∑' k, volume (E k) = ∑' j, j * volume (levelSet E j)` chains: Tonelli (Step 1: sum of measures = integral of counting function) → level set decomposition (Step 5: counting function = sum over levels) → Tonelli again (Step 6: integral of level decomposition = weighted sum of level measures).
- The j = 0 term contributes 0 · m(F\_0) = 0, so the sum over j ≥ 0 equals the sum over j ≥ 1.
- `Pairwise (Disjoint on levelSet E)` states the level sets are pairwise disjoint.

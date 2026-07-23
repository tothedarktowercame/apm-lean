

# APM a02J01: Schur's test for L² boundedness of integral operators

## Why It's Hard

You need to show an integral operator Tu(x) = ∫ k(x,y)u(y) dy is bounded on L² with norm ≤ 1, given only L¹ bounds on the kernel in each variable separately. The L¹ bounds control the kernel's "row sums" and "column sums," but L² boundedness involves the *interaction* between both variables simultaneously. You can't just apply Cauchy-Schwarz in one variable — that loses a factor. The trick is to apply Cauchy-Schwarz with a strategically chosen weight, exploiting both bounds simultaneously.

## The Key Insight

Split the kernel as |k(x,y)| = |k(x,y)|^{1/2} · |k(x,y)|^{1/2} and apply Cauchy-Schwarz to the integral ∫ k(x,y) u(y) dy, using one factor of |k|^{1/2} with |u(y)| and the other factor of |k|^{1/2} alone. The "column sum" bound controls the second factor, and the "row sum" bound controls the remaining integral when you square and integrate in x. This is **Schur's test** with the test function h ≡ 1.

## Complete Proof

**Theorem.** Let k : ℝⁿ × ℝⁿ → ℝ be measurable with ∫|k(x,y)| dx ≤ 1 for a.e. y and ∫|k(x,y)| dy ≤ 1 for a.e. x. Then for u ∈ L²(ℝⁿ):

$$\left\|\int_{\mathbb{R}^n} k(\cdot, y) u(y)\,dy\right\|_{L^2} \leq \|u\|_{L^2}.$$

**Proof.**

Define Tu(x) = ∫ k(x,y) u(y) dy. We need to show ||Tu||₂ ≤ ||u||₂.

**Step 1: Pointwise bound via Cauchy-Schwarz.**

For each x, write:

$$|Tu(x)| \leq \int |k(x,y)| \cdot |u(y)|\,dy = \int |k(x,y)|^{1/2} \cdot |k(x,y)|^{1/2} |u(y)|\,dy.$$

Apply Cauchy-Schwarz to the functions g₁(y) = |k(x,y)|^{1/2} and g₂(y) = |k(x,y)|^{1/2} |u(y)|:

$$|Tu(x)| \leq \left(\int |k(x,y)|\,dy\right)^{1/2} \cdot \left(\int |k(x,y)| |u(y)|^2\,dy\right)^{1/2}.$$

By hypothesis, ∫|k(x,y)| dy ≤ 1 for a.e. x. So:

$$|Tu(x)|^2 \leq 1 \cdot \int |k(x,y)| |u(y)|^2\,dy = \int |k(x,y)| |u(y)|^2\,dy.$$

**Step 2: Integrate in x and apply Fubini.**

$$\|Tu\|_2^2 = \int |Tu(x)|^2\,dx \leq \int\left(\int |k(x,y)| |u(y)|^2\,dy\right) dx.$$

By Tonelli's theorem (all terms nonneg):

$$= \int |u(y)|^2 \left(\int |k(x,y)|\,dx\right) dy \leq \int |u(y)|^2 \cdot 1\,dy = \|u\|_2^2.$$

The last inequality uses ∫|k(x,y)| dx ≤ 1 for a.e. y.

Therefore ||Tu||₂ ≤ ||u||₂. ∎

## What Connects

**To Schur's test.** This is the simplest case of Schur's test. The general version says: if there exists a positive measurable function h such that ∫|k(x,y)| h(y)^q dy ≤ C^q h(x)^q and ∫|k(x,y)| h(x)^p dx ≤ C^p h(y)^p, then T is bounded on Lʳ for appropriate r. Our problem is h ≡ 1, p = q = 2, C = 1.

**To Young's convolution inequality.** If k(x,y) = κ(x-y) (a convolution kernel), then the row/column bounds become ||κ||₁ ≤ 1, and the conclusion ||κ * u||₂ ≤ ||u||₂ is a special case of Young's inequality (||f * g||\_r ≤ ||f||\_p ||g||\_q with 1/p + 1/q = 1 + 1/r; here p = 1, q = r = 2).

**To the Cauchy-Schwarz splitting trick.** The idea of writing |k|^{1/2} · |k|^{1/2} and applying C-S is a workhorse technique. It appears in the Cotlar-Stein lemma, the T(1) theorem, and Calderón-Zygmund theory. The asymmetry — one factor absorbs |u|, the other is integrated alone — is what lets both kernel bounds be used.

**To interpolation.** The two hypotheses (row bound and column bound) can be viewed as: T is bounded on L^∞ (with norm 1, from the row bound) and on L¹ (with norm 1, from the column bound). By the Riesz-Thorin interpolation theorem, T is bounded on Lp for all 1 ≤ p ≤ ∞ with norm ≤ 1. The problem asks for the p = 2 case, which the direct Schur argument gives without interpolation.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic

open MeasureTheory Set Filter

noncomputable section

variable {n : ℕ}

/-- The integral operator Tu(x) = ∫ k(x,y) u(y) dy. -/
def integralOp (k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, k x y * u y ∂volume

/-- The "row bound" hypothesis: ∫ |k(x,y)| dy ≤ 1 for a.e. x. -/
def RowBound (k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)),
    ∫ y, ‖k x y‖ ∂volume ≤ 1

/-- The "column bound" hypothesis: ∫ |k(x,y)| dx ≤ 1 for a.e. y. -/
def ColBound (k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)),
    ∫ x, ‖k x y‖ ∂volume ≤ 1

/-- Cauchy-Schwarz splitting: |Tu(x)|² ≤ ∫ |k(x,y)| |u(y)|² dy
    using ∫ |k(x,y)| dy ≤ 1. -/
lemma integralOp_sq_le
    {k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry k))
    (hrow : RowBound k)
    {u : (Fin n → ℝ) → ℝ} (hu : Memℒp u 2 volume) :
    ∀ᵐ x ∂volume,
      (integralOp k u x) ^ 2 ≤ ∫ y, ‖k x y‖ * (u y) ^ 2 ∂volume := by
  sorry

/-- Tonelli step: ∫∫ |k(x,y)| |u(y)|² dy dx = ∫ |u(y)|² (∫|k(x,y)|dx) dy
    ≤ ∫ |u(y)|² dy. -/
lemma tonelli_bound
    {k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry k))
    (hcol : ColBound k)
    {u : (Fin n → ℝ) → ℝ} (hu : Memℒp u 2 volume) :
    ∫ x, (∫ y, ‖k x y‖ * (u y) ^ 2 ∂volume) ∂volume ≤
      ∫ y, (u y) ^ 2 ∂volume := by
  sorry

/-- Main theorem (Schur's test, h≡1 case):
    ‖Tu‖_{L²} ≤ ‖u‖_{L²}. -/
theorem schur_test_L2
    {k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry k))
    (hrow : RowBound k)
    (hcol : ColBound k)
    {u : (Fin n → ℝ) → ℝ} (hu : Memℒp u 2 volume) :
    eLpNorm (integralOp k u) 2 volume ≤ eLpNorm u 2 volume := by
  sorry

/-- Tu is in L² whenever u is. -/
theorem integralOp_memLp
    {k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry k))
    (hrow : RowBound k)
    (hcol : ColBound k)
    {u : (Fin n → ℝ) → ℝ} (hu : Memℒp u 2 volume) :
    Memℒp (integralOp k u) 2 volume := by
  sorry

/-- The integral operator as a bounded linear map on L². -/
def integralOpBounded
    {k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry k))
    (hrow : RowBound k) (hcol : ColBound k) :
    Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
    Lp ℝ 2 (volume : Measure (Fin n → ℝ)) := by
  sorry

/-- The operator norm is at most 1. -/
theorem integralOpBounded_norm_le
    {k : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry k))
    (hrow : RowBound k) (hcol : ColBound k) :
    ‖integralOpBounded hk hrow hcol‖ ≤ 1 := by
  sorry

end
```

**Mathlib notes:**

- `Fin n → ℝ` is the standard Mathlib type for ℝⁿ. `volume` on this type is the product Lebesgue measure.
- `Function.uncurry k : (Fin n → ℝ) × (Fin n → ℝ) → ℝ` uncurries k for the joint measurability hypothesis.
- `eLpNorm u 2 volume` is the L² norm (formerly `snorm`). The statement `eLpNorm (integralOp k u) 2 volume ≤ eLpNorm u 2 volume` encodes ||Tu||₂ ≤ ||u||₂.
- `Memℒp u 2 volume` says u ∈ L²(ℝⁿ).
- `RowBound` and `ColBound` use `∀ᵐ x ∂volume` (for a.e. x) and `∫ y, ‖k x y‖` (Bochner integral of the norm).
- `→L[ℝ]` is `ContinuousLinearMap ℝ`, the type of bounded linear operators. `integralOpBounded` packages the operator with its boundedness proof.
- The proof chain: `integralOp_sq_le` (Cauchy-Schwarz splitting, uses row bound) → `tonelli_bound` (Fubini/Tonelli, uses column bound) → `schur_test_L2` (combine and take square roots).

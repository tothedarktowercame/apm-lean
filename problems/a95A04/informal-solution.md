

# APM a95A04: Symmetric mean value property implies f is constant a.e.

## 1. Informal proof

**Why it's hard.** The hypothesis $\int_{x-h}^x f = \int_x^{x+h} f$ (symmetric averages agree) is a weak integral condition that must be upgraded to the pointwise conclusion $f =$ constant a.e. The function is only $L^{1}$, so pointwise statements require the Lebesgue differentiation theorem, and the constancy must be extracted from the symmetry condition.

**The key insight.** The symmetry condition says $\int_{x-h}^{x+h} f = 2\int_x^{x+h} f$, meaning the integral of $f$ over any interval centered at $x$ equals twice the integral over the right half. This forces $f$ to have equal averages on all dyadic intervals of the same length, and by induction on the dyadic level, $\int_I f = m(I) \cdot \int_0^1 f$ for every dyadic interval $I$. The Lebesgue differentiation theorem then gives $f(x) = \int_0^1 f$ a.e.

**Proof.**

Let $c = \int_0^1 f(t) dt$. We show $\int_I f = c \cdot m(I)$ for every dyadic interval $I = [k2^{-j}, (k+1)2^{-j}]$, then use Lebesgue differentiation.

*Step 1: Base case $j = 0$.* $I = [0,1]$, $\int_I f = c \cdot 1$. ✓

*Step 2: Dyadic splitting.* For $I = [a, b]$ with midpoint $x = (a+b)/2$ and $h = (b-a)/2$:

The hypothesis gives $\int_{x-h}^x f = \int_x^{x+h} f$, i.e., $\int_a^x f = \int_x^b f$.

Since $\int_a^b f = \int_a^x f + \int_x^b f = 2 \int_a^x f$, we get $\int_a^x f = (1/2)\int_a^b f$ and $\int_x^b f = (1/2)\int_a^b f$.

So if $\int_I f = c \cdot m(I)$, then each half of $I$ also satisfies $\int_{\text{half}} f = (1/2) \cdot c \cdot m(I) = c \cdot m(\text{half})$. ✓

*Step 3: Induction.* By induction on $j$: for $j = 0$, $\int_{[0,1]} f = c$. Splitting $[0,1]$ into $[0,1/2]$ and $[1/2,1]$ using Step 2 with $x = 1/2$, $h = 1/2$: $\int_{[0,1/2]} f = c/2 = c \cdot m([0,1/2])$. Similarly $\int_{[1/2,1]} f = c/2$. Continuing: at level $j$, every dyadic interval $I$ of length $2^{-j}$ satisfies $\int_I f = c \cdot 2^{-j} = c \cdot m(I)$. ✓

*Step 4: Lebesgue differentiation.* For a.e. $x \in [0,1]$, the Lebesgue differentiation theorem gives:

$f(x) = \lim_{m(I)\to 0, x\in I} (1/m(I)) \int_I f$.

Taking $I$ to be the dyadic interval of level $j$ containing $x$ (so $m(I) = 2^{-j} \to 0$):

$f(x) = \lim_{j\to\infty} (1/2^{-j}) \cdot c \cdot 2^{-j} = c = \int_0^1 f(t) dt$. ✓ ∎

**What connects.** This problem combines the dyadic structure of $[0,1]$ with the Lebesgue differentiation theorem. The symmetry condition forces $f$ to have constant averages on all dyadic intervals, and the Lebesgue differentiation theorem upgrades this to a.e. pointwise constancy. The result is a uniqueness theorem: the only $L^{1}$ function satisfying the symmetric mean value property on $[0,1]$ is the constant function. This connects to the mean value property for harmonic functions (where symmetric averages over spheres equal the center value) and to the theory of martingales (the dyadic averages form a martingale that converges a.e. to $f$ by the martingale convergence theorem, which is equivalent to Lebesgue differentiation in this context).

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Decomposition.LebesgueDecomposition
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set intervalIntegral Filter

noncomputable section

/-- The symmetric mean value hypothesis:
    ∫_{x-h}^x f = ∫_x^{x+h} f whenever [x-h, x+h] ⊆ [0,1]. -/
def SymmetricMeanValue (f : ℝ → ℝ) : Prop :=
  ∀ x h : ℝ, 0 < h → Icc (x - h) (x + h) ⊆ Icc 0 1 →
    ∫ t in (x - h)..x, f t = ∫ t in x..(x + h), f t

/-- Main theorem: f equals its average a.e. -/
theorem constant_of_symmetric_mean_value
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    (hsym : SymmetricMeanValue f) :
    f =ᵐ[volume.restrict (Icc 0 1)]
      fun _ => ∫ t in (0:ℝ)..1, f t := by
  sorry

/-- Dyadic intervals have the correct average:
    ∫_{k/2^j}^{(k+1)/2^j} f = c · 2^{-j}. -/
lemma dyadic_integral_eq
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume)
    (hsym : SymmetricMeanValue f)
    (j : ℕ) (k : ℕ) (hk : k < 2 ^ j) :
    ∫ t in (↑k / 2 ^ j : ℝ)..(↑(k + 1) / 2 ^ j), f t =
      (∫ t in (0:ℝ)..1, f t) / 2 ^ j := by
  sorry

/-- Splitting step: if ∫_a^b f = c·(b-a), then ∫_a^{(a+b)/2} f = c·(b-a)/2. -/
lemma symmetric_split
    {f : ℝ → ℝ}
    (hsym : SymmetricMeanValue f)
    {a b : ℝ} (hab : a < b)
    (h_sub : Icc a b ⊆ Icc 0 1) :
    ∫ t in a..((a + b) / 2), f t = (1 / 2) * ∫ t in a..b, f t := by
  sorry

/-- Lebesgue differentiation: the average of f over shrinking
    intervals converges to f(x) a.e. -/
lemma lebesgue_differentiation_intervals
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc 0 1) volume) :
    ∀ᵐ x ∂(volume.restrict (Icc 0 1)),
      Tendsto (fun j : ℕ =>
        2 ^ j * ∫ t in (⌊x * 2^j⌋ / 2^j : ℝ)..((⌊x * 2^j⌋ + 1) / 2^j), f t)
        atTop (𝓝 (f x)) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.IntegrableOn f (Icc 0 1) volume` — $f \in L^{1}([0,1])$
- `intervalIntegral` / `∫ t in a..b, f t` — interval integral
- `Filter.EventuallyEq` / `=ᵐ[μ]` — a.e. equality
- `Measure.restrict (Icc 0 1)` — restricted measure
- `Filter.atTop` — for $j \to \infty$ in dyadic refinement

**Key lemmas:**
- `intervalIntegral.integral_add_adjacent_intervals` — $\int_a^b + \int_b^c = \int_a^c$. Used for the splitting step: $\int_a^b = \int_a^x + \int_x^b$
- `intervalIntegral.integral_symm` — $\int_a^b = -\int_b^a$
- `MeasureTheory.ae_restrict_of_ae` — transferring a.e. statements to restricted measures
- Lebesgue differentiation theorem — `MeasureTheory.Measure.ae_tendsto_average` or related. The key tool for Step 4
- `Nat.floor_div_mul_add_mod_eq` — relating $\lfloor x\cdot 2^{j}\rfloor$ to dyadic intervals
- `pow_pos` — $2^j > 0$
- `div_lt_div_right` — arithmetic with dyadic fractions

**Tactic hints:**
- `induction j with | zero => ... | succ j ih => ...` — induction on the dyadic level
- `have hsplit := symmetric_split hsym ...` — applying the splitting lemma
- `simp [intervalIntegral.integral_add_adjacent_intervals]` — combining adjacent integrals
- `field_simp` — for $k/2^j$ arithmetic
- `norm_num` — for $2^j$ computations
- `linarith` — for interval containment conditions
- `filter_upwards [lebesgue_differentiation_intervals hf]` — passing to the a.e. limit
- `ring` — for $c/2^j = c \cdot 2^{-j}$ type simplifications
- `exact?` — finding the Lebesgue differentiation theorem

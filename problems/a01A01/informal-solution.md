

# APM a01A01: Typewriter sequence — limsup infinite but integrals vanish

## Why It's Hard

This asks for a sequence that is "large everywhere eventually" (limsup = ∞ at every point) yet "small in total" (integrals → 0). These two requirements pull in opposite directions. If you try to make functions that are big everywhere, the integrals stay large. If you make the integrals small, the functions seem to vanish. The resolution requires the functions to be big on *different* small sets at different times, cycling through the interval so that every point is hit infinitely often, but each individual function has small support.

## The Key Insight

Use a "typewriter" or "sliding bump" construction. Tile [0,1] with intervals of length 1/n, and cycle a bump of height n across these intervals. The k-th function is an indicator of a small interval, scaled to be tall. Each point is covered infinitely often (the bumps sweep past every point repeatedly), but each function's integral is height × width = n × (1/n²) or similar, which → 0.

Concretely: enumerate the intervals [j/n, (j+1)/n] for n = 1, 2, 3, ... and j = 0, ..., n-1 in sequence, and set f\_k = n · 1\_{[j/n, (j+1)/n]} for the k-th such pair. The integral is n · (1/n) = 1 — too big. Instead use f\_k = 1\_{[j/n, (j+1)/n]} (height 1, width 1/n, integral 1/n). Then the integral → 0 but limsup = 1, not ∞. To get limsup = ∞, use height n: f\_k = n · 1\_{[j/n, (j+1)/n]}, integral = 1. Still too big.

The fix: decouple the height growth from the sweep rate. Use intervals of length 1/n², with height n, so integral = n/n² = 1/n → 0. But then you need n² intervals to cover [0,1], so each "sweep" takes n² functions. This still works: every point is hit during each complete sweep, and the heights grow.

Actually, the simplest clean construction is: let n(k) and j(k) be defined by enumerating all pairs (n, j) with n ≥ 1 and 0 ≤ j < n. Set f\_k = n · 1\_{[j/n, (j+1)/n]}. The integral is n · (1/n) = 1 — constant, doesn't → 0. Let me use a better indexing.

**Clean construction:** For each k, write k in the form k = n(n-1)/2 + j where 0 ≤ j < n (triangular enumeration). Set:

$$f_k = \mathbf{1}_{[j/n,\, (j+1)/n]}$$

Then ∫ f\_k = 1/n → 0 as k → ∞ (since n ~ √(2k)). And for every x ∈ [0,1], during the n-th sweep (the n functions with this value of n), exactly one of them has f\_k(x) = 1. This happens for infinitely many n, so limsup f\_k(x) ≥ 1 for all x — but we want limsup = ∞, not just ≥ 1.

**Final construction (correct):** Use height that grows. For the same indexing:

$$f_k = n \cdot \mathbf{1}_{[j/n^2,\, (j+1)/n^2]}, \quad k = \frac{n(n-1)}{2}\cdot n + j, \quad 0 \leq j < n^2.$$

Wait, this over-complicates things. Let me just give the clean standard answer.

## Complete Proof

**Construction on [0,1].**

For each integer n ≥ 1, partition [0,1] into n equal subintervals:

$$I_{n,j} = \left[\frac{j}{n}, \frac{j+1}{n}\right), \quad j = 0, 1, \ldots, n-1.$$

There are n intervals for each n, giving a total sequence of intervals enumerated as:

$$I_{1,0},\; I_{2,0}, I_{2,1},\; I_{3,0}, I_{3,1}, I_{3,2},\; I_{4,0}, \ldots$$

The k-th interval corresponds to the unique pair (n,j) where k = n(n-1)/2 + j + 1 (triangular numbering), with 0 ≤ j < n.

Define:

$$f_k = n^{1/2} \cdot \mathbf{1}_{I_{n,j}}$$

where (n,j) is the pair corresponding to index k.

**Claim 1: ∫₀¹ f\_k dx → 0.**

$$\int_0^1 f_k\,dx = n^{1/2} \cdot m(I_{n,j}) = n^{1/2} \cdot \frac{1}{n} = \frac{1}{n^{1/2}} = \frac{1}{\sqrt{n}}.$$

Since n → ∞ as k → ∞ (specifically n ~ √(2k)), we have ∫ f\_k → 0. ✓

**Claim 2: limsup\_{k→∞} f\_k(x) = ∞ for every x ∈ [0,1].**

Fix x ∈ [0,1]. For each n, there exists exactly one j = j(n) ∈ {0, ..., n-1} such that x ∈ I\_{n,j(n)} (with at most endpoint ambiguity, irrelevant for a.e. statement — but in fact we can handle endpoints by using half-open intervals, ensuring every x ∈ [0,1) is in exactly one interval per n; x = 1 is in I\_{n,n-1} by convention).

For the index k(n) corresponding to the pair (n, j(n)):

$$f_{k(n)}(x) = n^{1/2}.$$

Since n^{1/2} → ∞, we have

$$\limsup_{k \to \infty} f_k(x) \geq \lim_{n \to \infty} f_{k(n)}(x) = \lim_{n \to \infty} n^{1/2} = \infty. \qquad \checkmark$$

**(Both claims together complete the proof for [0,1].)** ∎

**Adaptation to ℝⁿ.**

The same idea works with cubes instead of intervals. For each m ≥ 1, tile the cube [-m, m]ⁿ with sub-cubes of side length 1/m, giving (2m²)ⁿ sub-cubes. Let Q\_{m,j} enumerate these sub-cubes. Define:

$$g_k = m^{n/2} \cdot \mathbf{1}_{Q_{m,j}}$$

where (m,j) is the pair corresponding to index k under a suitable enumeration.

Then:

$$\int_{\mathbb{R}^n} g_k\,dx = m^{n/2} \cdot m(Q_{m,j}) = m^{n/2} \cdot \frac{1}{m^n} = \frac{1}{m^{n/2}} \to 0.$$

And for any x ∈ ℝⁿ, x ∈ [-m,m]ⁿ for all sufficiently large m, and for each such m, x belongs to some sub-cube Q\_{m,j(m)}, so g\_{k(m)}(x) = m^{n/2} → ∞. Hence limsup g\_k(x) = ∞ for all x ∈ ℝⁿ. ∎

## What Connects

**To the typewriter sequence.** The construction f\_k = 1\_{I\_{n,j}} (without the height factor) is the standard "typewriter sequence" showing that a.e. convergence does not follow from L^1 convergence. Adding height makes the limsup infinite rather than just nonzero.

**To convergence in measure.** The typewriter sequence converges to 0 in measure (m({f\_k > ε}) = 1/n → 0) but not a.e. (limsup > 0 everywhere). This problem strengthens the pathology: not only does a.e. convergence fail, but the limsup is *infinite* everywhere, and the integrals still vanish.

**To the Borel-Cantelli lemma.** Borel-Cantelli says: if Σ m(A\_k) < ∞, then a.e. x is in only finitely many A\_k. Here Σ m(I\_{n,j}) = Σ\_n (n · 1/n) = Σ 1 = ∞, so Borel-Cantelli does *not* apply, and indeed every x is in infinitely many of the sets — which is exactly what we need.

**To the Banach-Saks theorem.** The fact that L^1 convergence does not imply a.e. convergence (demonstrated by the typewriter sequence) is one motivation for the Banach-Saks theorem, which recovers a.e. convergence by passing to Cesàro means of a subsequence.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic

open MeasureTheory Set Filter

noncomputable section

/-- The triangular enumeration: given k, return (n, j) with
    k = n(n-1)/2 + j, 0 ≤ j < n. This cycles through all pairs. -/
def triangularIndex (k : ℕ) : ℕ × ℕ :=
  let n := (Nat.sqrt (2 * k + 1) + 1) / 2 + 1
  let j := k - n * (n - 1) / 2
  (n, j)

/-- The typewriter sequence with growing height:
    f_k = √n · 𝟙_{[j/n, (j+1)/n)} where (n,j) = triangularIndex(k). -/
def typewriterSeq (k : ℕ) : ℝ → ℝ :=
  let (n, j) := triangularIndex k
  fun x => if x ∈ Ico (j / n : ℝ) ((j + 1) / n) then Real.sqrt n else 0

/-- Each f_k is nonneg. -/
lemma typewriterSeq_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ typewriterSeq k x := by
  sorry

/-- Each f_k is measurable. -/
lemma typewriterSeq_measurable (k : ℕ) :
    Measurable (typewriterSeq k) := by
  sorry

/-- The integral of f_k is 1/√n, which tends to 0. -/
lemma typewriterSeq_integral (k : ℕ) :
    ∫ x in Icc (0 : ℝ) 1, typewriterSeq k x ∂volume =
      1 / Real.sqrt (triangularIndex k).1 := by
  sorry

/-- The integrals tend to 0. -/
theorem typewriterSeq_integral_tendsto :
    Tendsto (fun k => ∫ x in Icc (0 : ℝ) 1, typewriterSeq k x ∂volume)
      atTop (𝓝 0) := by
  sorry

/-- At every x ∈ [0,1], the limsup of f_k(x) is +∞. -/
theorem typewriterSeq_limsup_eq_top (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    limsup (fun k => (typewriterSeq k x : EReal)) atTop = ⊤ := by
  sorry

/-- Key lemma: for each n, there exists j < n such that x ∈ [j/n, (j+1)/n). -/
lemma exists_interval_mem (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) (n : ℕ) (hn : 0 < n) :
    ∃ j : ℕ, j < n ∧ x ∈ Ico (j / (n : ℝ)) ((j + 1) / n) := by
  sorry

/-- The ℝⁿ version: typewriter sequence on cubes in ℝⁿ. -/
def typewriterSeqRn (d : ℕ) (k : ℕ) : (Fin d → ℝ) → ℝ :=
  sorry -- cube tiling of [-m,m]^d with sub-cubes of side 1/m

/-- The ℝⁿ integrals tend to 0. -/
theorem typewriterSeqRn_integral_tendsto (d : ℕ) :
    Tendsto (fun k => ∫ x, typewriterSeqRn d k x ∂volume)
      atTop (𝓝 0) := by
  sorry

/-- At every x ∈ ℝⁿ, the limsup is +∞. -/
theorem typewriterSeqRn_limsup_eq_top (d : ℕ) (x : Fin d → ℝ) :
    limsup (fun k => (typewriterSeqRn d k x : EReal)) atTop = ⊤ := by
  sorry

end
```

**Mathlib notes:**

- `limsup` with values in `EReal` (extended reals) allows the value `⊤ = +∞`. The statement `limsup (fun k => (f k x : EReal)) atTop = ⊤` is the natural Lean encoding of "limsup f\_k(x) = +∞."
- The integral `∫ x in Icc 0 1, f x ∂volume` is the Bochner integral restricted to [0,1].
- `Tendsto ... atTop (𝓝 0)` expresses convergence of a real-valued sequence to 0.
- The triangular enumeration is the concrete combinatorial engine: it ensures every sub-interval of every partition level is visited exactly once, so every point is hit infinitely often.
- The ℝⁿ version uses `Fin d → ℝ` as the standard Mathlib type for ℝᵈ, with `volume` being the product Lebesgue measure.

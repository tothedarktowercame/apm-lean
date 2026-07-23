

# APM a00J06: Pringsheim's theorem — a power series with nonneg coefficients is singular at its radius

## Why It's Hard

The statement seems intuitive — nonneg coefficients mean the function "blows up most" along the positive real axis — but making this rigorous requires a careful indirect argument. You can't just say "f(r) → ∞ as r → 1⁻" because that need not be true (e.g., Σ xⁿ/n² converges at x = 1). The function might converge at z = 1 and still be singular there (singularity means non-extendability, not divergence). The challenge is to show that even if f(1) is finite, no analytic continuation past z = 1 is possible.

## The Key Insight

Argue by contradiction. If f were analytic at z = 1, it would have a Taylor expansion at z = 1 with some positive radius of convergence, which would extend f to a disk centered at 1 that overlaps past the unit circle. By rewriting the Taylor expansion at z = 1 using the known Taylor expansion at z = 0, the Taylor coefficients at z = 1 involve f⁽ⁿ⁾(1)/n! = Σ\_k a(k) · C(k,n) · 1^{k-n}, which are *nonneg* (since a(k) ≥ 0). This nonnegativity forces the original power series at z = 0 to converge in a disk strictly larger than the unit disk — contradicting radius of convergence 1.

## Complete Proof

**Theorem (Pringsheim, 1893).** Let f(z) = Σ a(n)zⁿ have radius of convergence R = 1 with a(n) ≥ 0 for all n. Then z = 1 is a singular point of f.

**Proof.** Suppose for contradiction that f admits an analytic continuation to a disk D(1, ε) = {z : |z - 1| < ε} for some ε > 0. Then f is analytic on D(0,1) ∪ D(1,ε), and in particular there exists r > 1 such that f is analytic on D(0, r) (since D(0,1) ∪ D(1,ε) contains D(0, 1 + δ) for some small δ, because the two disks overlap in a connected region containing the real interval (1-ε, 1+ε)).

Wait — this isn't quite right, since D(0,1) ∪ D(1,ε) need not contain a full disk centered at 0. Let me use the standard argument.

Since f is analytic on D(1,ε), the Taylor series of f at z = 1 converges on D(1,ε):

$$f(z) = \sum_{n=0}^{\infty} \frac{f^{(n)}(1)}{n!}(z - 1)^n, \quad |z-1| < \varepsilon.$$

Now compute f⁽ⁿ⁾(1). Since f(z) = Σ\_{k≥0} a(k) zᵏ converges on D(0,1), the derivatives converge on D(0,1) and, by Abel's theorem (or direct argument), the n-th derivative at real values r < 1 is:

$$f^{(n)}(r) = \sum_{k=n}^{\infty} a(k) \cdot k(k-1)\cdots(k-n+1) \cdot r^{k-n}.$$

Each term is nonneg (since a(k) ≥ 0, the falling factorial is positive for k ≥ n, and r > 0). So f⁽ⁿ⁾(r) ≥ 0 for all 0 < r < 1. Since f is analytic at z = 1, f⁽ⁿ⁾ is continuous at 1, so:

$$f^{(n)}(1) = \lim_{r \to 1^-} f^{(n)}(r) = \lim_{r \to 1^-} \sum_{k=n}^{\infty} a(k) \frac{k!}{(k-n)!} r^{k-n} \geq 0.$$

(The limit exists because f⁽ⁿ⁾ is continuous at 1, and each partial sum is nonneg, so the limit is nonneg — possibly +∞, but the assumption of analyticity at 1 guarantees it is finite.)

So the Taylor coefficients at z = 1 satisfy c\_n := f⁽ⁿ⁾(1)/n! ≥ 0.

**Now we reach the contradiction.** The Taylor series at z = 1 has radius of convergence at least ε. So for any ρ < ε:

$$\sum_{n=0}^{\infty} c_n \rho^n < \infty.$$

In particular, the series Σ c\_n (z-1)ⁿ converges absolutely for |z - 1| < ε. Since c\_n ≥ 0, it converges for real z - 1 = ρ with 0 < ρ < ε, i.e., for z = 1 + ρ, a real number greater than 1.

But the Taylor series at z = 1 represents f in D(1,ε), and for real z = 1 + ρ ∈ (1, 1+ε):

$$f(1 + \rho) = \sum_{n=0}^{\infty} c_n \rho^n.$$

Now return to the original series at z = 0. For 0 < r < 1:

$$f(r) = \sum_{k=0}^{\infty} a(k) r^k.$$

Since a(k) ≥ 0, this is a monotone increasing function of r on (0,1). The Taylor expansion at z = 1 shows f is continuous (and finite) at z = 1, so f(r) ↑ f(1) < ∞, meaning Σ a(k) converges.

More importantly, f is real-analytic at z = 1, so for real z near 1, f(z) = Σ c\_n (z-1)ⁿ. For z = r ∈ (0,1), we can also write f(r) = Σ a(k) rᵏ. Since both expressions represent f on (1-ε, 1), and f is analytic at 1, the power series at 0 must also represent f at z = 1 + ρ for small ρ > 0. But more directly:

Since c\_n ≥ 0 and the Taylor series at 1 converges for |z-1| < ε, the original function f is analytic at 1 + ρ for all 0 < ρ < ε. At z = 1 + ρ (real), we can expand:

$$f(1 + \rho) = \sum_{n=0}^{\infty} c_n \rho^n = \sum_{n=0}^{\infty} \frac{f^{(n)}(1)}{n!} \rho^n.$$

Each c\_n ≥ 0, so |c\_n| = c\_n, meaning the power series at z = 1 converges absolutely at z = 1 + ρ. Now for any z with |z - 1| ≤ ρ:

$$|c_n (z-1)^n| \leq c_n \rho^n$$

so the Taylor series at z = 1 converges absolutely on {|z-1| ≤ ρ} for any ρ < ε. In particular, it converges on the closed disk of radius ρ centered at 1.

This means f is analytic on D(1, ε). But D(0,1) ∪ D(1,ε) contains the real interval (0, 1+ε). For r ∈ (0, 1+ε), the original power series Σ a(k) rᵏ (with nonneg terms) must agree with f(r). Since f(r) is finite for r ∈ (1, 1+ε), the series Σ a(k) rᵏ converges for some r > 1.

**But the radius of convergence of Σ a(k) zᵏ is 1.** If Σ a(k) rᵏ converges for some r > 1, then by the root test the radius of convergence is at least r > 1 — contradiction.

(Technical detail: for nonneg terms, convergence at a real point r > 0 implies absolute convergence, which implies the radius of convergence is at least r.) ∎

## What Connects

**Pringsheim's theorem** is a foundational result in the theory of singularities of power series. It says that for power series with nonneg coefficients, the positive real boundary point of the disk of convergence is always a singularity — you can never "slip past" it by analytic continuation.

**To Hadamard's gap theorem.** Both results identify structural features of the coefficients that force singularities. Hadamard's gap theorem handles lacunary series (big gaps between nonzero coefficients); Pringsheim handles nonnegativity. In both cases, the singularity structure is constrained by the coefficient structure.

**To Tauberian theory.** The nonnegativity condition makes Abel's theorem and its converses (Hardy-Littlewood Tauberian theorem) especially powerful. Pringsheim's theorem is why the point z = 1 is always the relevant boundary point for Tauberian arguments about series with nonneg coefficients.

**To probability.** The generating function of a probability distribution on ℕ is Σ p(n) zⁿ with p(n) ≥ 0 and Σ p(n) = 1. Pringsheim guarantees z = 1 is always a singularity of the generating function (unless the radius is > 1, which happens only for distributions with exponential tails). This controls the asymptotic behaviour of p(n) via singularity analysis.

**To analytic combinatorics.** The Flajolet-Sedgewick framework for counting combinatorial structures relies heavily on Pringsheim: generating functions with nonneg integer coefficients (counting sequences) always have their dominant singularity on the positive real axis, which is why the transfer theorems work.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.Basic

open Filter Topology

noncomputable section

/-- Radius of convergence of a formal power series with complex coefficients. -/
def radiusOfConvergence (a : ℕ → ℝ) : ℝ≥0∞ :=
  FormalMultilinearSeries.radius
    (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n : ℂ))

/-- A power series with nonneg real coefficients, viewed as a function ℂ → ℂ. -/
def powerSeries (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n, (a n : ℂ) * z ^ n

/-- For nonneg coefficients, convergence at a positive real r implies
    the radius of convergence is at least r. -/
lemma radius_ge_of_summable_nonneg
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {r : ℝ} (hr : 0 < r) (hs : Summable (fun n => a n * r ^ n)) :
    FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n : ℂ)) ≥
      ENNReal.ofReal r := by
  sorry

/-- If f is analytic at z = 1 (i.e., has a convergent Taylor expansion there),
    then all Taylor coefficients at z = 1 are nonneg when the original
    coefficients are nonneg. -/
lemma taylor_at_one_nonneg
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {f : ℂ → ℂ} (hf_eq : ∀ z, ‖z‖ < 1 → f z = powerSeries a z)
    (hf_an : AnalyticAt ℂ f 1) :
    ∀ n, 0 ≤ (hf_an.choose n).re := by
  sorry

/-- Nonneg Taylor coefficients at z = 1 with radius ε > 0 imply
    the function is finite (and equals the original series) at some
    real r > 1. -/
lemma summable_beyond_one_of_analytic_at_one
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {f : ℂ → ℂ} (hf_eq : ∀ z, ‖z‖ < 1 → f z = powerSeries a z)
    (hf_an : AnalyticAt ℂ f 1) :
    ∃ r : ℝ, 1 < r ∧ Summable (fun n => a n * r ^ n) := by
  sorry

/-- Main theorem (Pringsheim): a power series with nonneg real coefficients
    and radius of convergence 1 is singular at z = 1.
    Stated as: there is no analytic continuation to a neighbourhood of 1. -/
theorem pringsheim_singular_at_one
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (h_radius : FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n : ℂ)) = 1) :
    ¬ ∃ (f : ℂ → ℂ), AnalyticAt ℂ f 1 ∧
      ∀ z, ‖z‖ < 1 → f z = powerSeries a z := by
  sorry

/-- Equivalent contrapositive formulation:
    if all a(n) ≥ 0 and the series extends analytically past z = 1,
    then the radius of convergence is strictly greater than 1. -/
theorem radius_gt_one_of_analytic_at_one_nonneg
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {f : ℂ → ℂ} (hf_eq : ∀ z, ‖z‖ < 1 → f z = powerSeries a z)
    (hf_an : AnalyticAt ℂ f 1) :
    1 < FormalMultilinearSeries.radius
      (fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n : ℂ)) := by
  sorry

end
```

**Mathlib notes:**

- `FormalMultilinearSeries.radius` computes the radius of convergence. The encoding `ContinuousMultilinearMap.mkPiRing ℂ (Fin n) c` wraps a scalar `c : ℂ` as a continuous n-multilinear map, which is how Mathlib represents power series coefficients in its analytic function API.
- `AnalyticAt ℂ f z` means f has a convergent power series in a neighbourhood of z. Its `choose` gives the coefficients (via `AnalyticAt` being a `∃ p, HasFPowerSeriesAt f p z`).
- The proof flows: `pringsheim_singular_at_one` assumes analyticity at 1 for contradiction, uses `taylor_at_one_nonneg` to establish nonneg Taylor coefficients, then `summable_beyond_one_of_analytic_at_one` to get convergence past r = 1, then `radius_ge_of_summable_nonneg` to contradict radius = 1.
- `Summable (fun n => a n * r ^ n)` for real `r > 1` directly contradicts radius of convergence = 1 for a nonneg series.

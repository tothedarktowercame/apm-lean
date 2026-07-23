<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98A01: Dilation family k^α f(k|x|) — thresholds for uniform, a.e., and L¹ convergence

## Why It's Hard

The family F_k(x) = k^α f(k|x|) is a **concentrating dilation**: as k → ∞ the profile f(k|x|) squeezes toward the origin while the prefactor k^α inflates or deflates it. The three convergence modes probe completely different features of this competition, so they have **three different thresholds** — and the L¹ threshold even depends on the dimension n, with a regime where the functions are *not integrable at all*. What makes the bookkeeping work is that f is pinned at **both ends**:

- f(t)/t → 1 as t → 0  ⟹  f(t) ≈ t near 0 (so f(0) = 0 and f is small near the origin);
- t⁴ f(t) → 1 as t → ∞  ⟹  f(t) ≈ t⁻⁴ at infinity (polynomial decay).

Each mode reads off a *different* one of these facts: uniform convergence sees the global maximum, a.e. convergence sees the t⁻⁴ tail (because k|x| → ∞ for fixed x ≠ 0), and L¹ convergence sees both ends through an integral whose finiteness hinges on the tail vs. the dimension.

Throughout, write r = |x|, and note f is continuous and positive on (0,∞) with f → 0 at both 0 and ∞, so M := sup_{t ≥ 0} f(t) is a finite positive number, attained.

## The Key Insight

- **Uniform**: sup_x f(k|x|) is *scale-invariant* — as |x| ranges over [0,∞) so does k|x| — so ‖F_k‖_∞ = M·k^α, and only the sign of α matters.
- **A.e.**: for *fixed* x ≠ 0, k|x| → ∞, so the t⁴f(t) → 1 asymptotic gives F_k(x) ≈ k^{α-4}|x|⁻⁴; the exponent α − 4 decides the pointwise limit.
- **L¹**: the substitution s = k|x| turns the radial integral into ‖F_k‖₁ = c_n k^{α-n}·∫₀^∞ f(s)s^{n-1}ds, decoupling the k-power (exponent α − n) from a fixed integral whose convergence at ∞ needs the s⁻⁴ tail to beat s^{n-1}, i.e. n ≤ 3.

## Complete Proof

**Answer.**

| mode | condition for F_k → 0 |
|------|------------------------|
| (a) uniform | α < 0 (every n) |
| (b) a.e. | α < 4 (every n) |
| (c) L¹(ℝⁿ) | α < n if n ≤ 3; **no α** if n ≥ 4 (then F_k ∉ L¹) |

### (a) Uniform convergence

For each fixed k > 0, as x ranges over ℝⁿ the argument k|x| ranges over all of [0,∞), so

$$\|F_k\|_\infty = \sup_{x \in \mathbb{R}^n} k^\alpha f(k|x|) = k^\alpha \sup_{s \geq 0} f(s) = M\,k^\alpha .$$

Since 0 < M < ∞, we have ‖F_k‖_∞ → 0 iff k^α → 0 iff **α < 0**. (At α = 0, ‖F_k‖_∞ = M > 0 for all k; at α > 0 it diverges.)

### (b) Almost-everywhere convergence

At x = 0 (a single point, hence negligible), F_k(0) = k^α f(0) = 0.

Fix x ≠ 0, so r = |x| > 0 and k r → ∞ as k → ∞. From t⁴ f(t) → 1 we may write f(kr) = (kr)^{-4}(1 + o(1)) as k → ∞, hence

$$F_k(x) = k^\alpha f(kr) = k^\alpha (kr)^{-4}(1 + o(1)) = k^{\alpha - 4}\, r^{-4}(1 + o(1)).$$

For fixed r > 0 this tends to 0 iff α − 4 < 0; if α = 4 it tends to r⁻⁴ ≠ 0, and if α > 4 it diverges. So F_k(x) → 0 for every x ≠ 0 iff α < 4, and the exceptional point x = 0 already gives 0. Therefore

- α < 4: F_k → 0 everywhere, in particular **a.e.**;
- α = 4: F_k → r⁻⁴ ≠ 0 for a.e. x, so it does **not** converge to 0 a.e.;
- α > 4: F_k diverges a.e.

Hence (b) holds iff **α < 4**.

### (c) L¹ convergence

All quantities are nonnegative, so Tonelli justifies the computation. Writing the integral in polar coordinates with c_n = |S^{n-1}| the surface area of the unit sphere, and substituting s = k r (r = s/k, dr = ds/k):

$$
\|F_k\|_{1} = \int_{\mathbb{R}^n} k^\alpha f(k|x|)\,dx
 = c_n \int_0^\infty k^\alpha f(kr)\, r^{n-1}\,dr
 = c_n\, k^{\alpha} \int_0^\infty f(s)\Big(\tfrac{s}{k}\Big)^{n-1}\tfrac{ds}{k}
 = c_n\, k^{\alpha - n} \underbrace{\int_0^\infty f(s)\, s^{n-1}\,ds}_{=: \,I_n}.
$$

So **‖F_k‖₁ = c_n k^{α-n} I_n**, with the k-dependence isolated in the power α − n and I_n independent of k.

**Finiteness of I_n.** The integrand g(s) = f(s) s^{n-1} is continuous and positive on (0,∞); convergence of I_n is decided at the two ends:

- **near 0**: f(s) ≈ s, so g(s) ≈ s^{n}, and ∫_0 s^{n}\,ds converges for every n ≥ 1;
- **at ∞**: f(s) ≈ s⁻⁴, so g(s) ≈ s^{n-5}, and ∫^∞ s^{n-5}\,ds converges iff n − 5 < −1, i.e. **n ≤ 3**.

Thus I_n is finite (and positive) iff n ∈ {1, 2, 3}, and I_n = +∞ for n ≥ 4.

**Conclusion for (c).**

- If **n ≤ 3**: I_n ∈ (0, ∞) is a fixed constant, so ‖F_k‖₁ = (c_n I_n)\,k^{α-n} → 0 iff α − n < 0, i.e. **α < n**. (At α = n the norm is a positive constant; at α > n it diverges.)
- If **n ≥ 4**: for *every* k the integral ∫₀^∞ f(kr) r^{n-1} dr diverges (same s^{n-5} tail), so ‖F_k‖₁ = ∞ — the functions F_k are **not in L¹(ℝⁿ) at all**, and "F_k → 0 in L¹" holds for **no** value of α.

$\blacksquare$

## What Connects

**Within analysis**: This is the standard "approximate-identity vs. spreading" dichotomy for dilations g_k(x) = k^α g(k x). The three thresholds (0, 4, and n) are the signatures of three norms scaling differently under dilation on ℝⁿ: L^∞ is scale-invariant in the profile (only k^α survives), pointwise values follow the decay exponent at ∞, and the L¹ mass scales like k^{α-n} because dx carries n powers of the dilation. The n ≥ 4 obstruction is the familiar fact that a t⁻⁴ radial tail is L¹ near ∞ only below dimension 4 (s^{n-1}·s⁻⁴ integrable ⟺ n < 4).

**The reusable move**: when a quantity is a dilation k^α g(k·), push the dilation onto the variable (s = k|x|) to separate a clean power k^{α - (\text{norm's homogeneity})} from a fixed, scale-free integral; finiteness of that integral is then a pure two-ends asymptotics question. The same computation underlies why δ-sequences, heat kernels, and Sobolev-critical bubbles have the exponents they do.

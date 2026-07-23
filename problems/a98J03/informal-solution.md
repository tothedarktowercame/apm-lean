<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98J03: The Poisson kernel as an L² contraction family converging to the identity

## Why It's Hard

The map is convolution against the **Poisson kernel**

$$P_y(x) = \frac{1}{\pi}\,\frac{y}{x^2 + y^2}, \qquad g_y = P_y * f,$$

the harmonic extension of f to the upper half-plane. (The printed denominator "(x−t) + y²" is a typo for "(x−t)² + y²": only with the square is P_y the Poisson kernel, and only then are (a)–(c) true.) Three separate things must be controlled at once: that the defining integral even converges and lands back in L²; that the resulting operators are bounded **uniformly in y** (not just for each fixed y); and that as y → 0 — precisely when the kernel sharpens toward a point mass δ₀ — the outputs reconverge to f. The hazard is that P_y degenerates as y → 0, so a naive estimate gives a constant that blows up. The cure is to move to the Fourier side, where convolution becomes multiplication and the whole family becomes a single, transparent multiplier.

## The Key Insight

Under the Fourier transform f̂(ξ) = ∫ f(x) e^{-2πi xξ} dx, the Poisson kernel transforms to

$$\widehat{P_y}(\xi) = e^{-2\pi y|\xi|},$$

so by the convolution theorem ĝ_y(ξ) = e^{-2π y|ξ|} f̂(ξ). The operator f ↦ g_y is just **multiplication of f̂ by the multiplier m_y(ξ) = e^{-2π y|ξ|}**, and everything follows from two facts about this multiplier:

- 0 < m_y(ξ) ≤ 1 for all ξ and all y > 0 — a **contraction** — giving (a) and a y-independent bound (b);
- m_y(ξ) → 1 pointwise as y → 0, dominated by 1 — giving (c) by dominated convergence.

## Complete Proof

**The kernel.** P_y(x) = (1/π) y/(x²+y²) is nonnegative and a probability density:

$$\int_{\mathbb{R}} P_y(x)\,dx = \frac{1}{\pi}\int_{\mathbb{R}} \frac{y}{x^2+y^2}\,dx \overset{x = yu}{=} \frac{1}{\pi}\int_{\mathbb{R}} \frac{du}{u^2+1} = 1,$$

so ‖P_y‖_{L¹} = 1. Its Fourier transform is the standard computation \widehat{P_y}(ξ) = e^{-2π y|ξ|}.

### (a) g_y ∈ L²(ℝ), and (b) bounded operators

For f ∈ L² and P_y ∈ L¹, the convolution integral converges for a.e. x and **Young's inequality** gives

$$\|g_y\|_2 = \|P_y * f\|_2 \leq \|P_y\|_1\,\|f\|_2 = \|f\|_2 < \infty. \tag{$\ast$}$$

So g_y ∈ L²(ℝ), proving (a). The map T_y : f ↦ g_y is linear (convolution is linear in f), and ($\ast$) says ‖T_y f‖_2 ≤ ‖f‖_2 for all f, i.e. T_y is a bounded operator L² → L² with operator norm

$$\|T_y\| \leq 1 \qquad \text{for every } y > 0,$$

a bound **independent of y** (in fact ‖T_y‖ = 1, since the multiplier m_y has sup 1). This proves (b).

*(Fourier-side check of (a), for transparency:* by Plancherel ‖f‖_2 = ‖f̂‖_2, and ĝ_y = m_y f̂ with |m_y| ≤ 1, so ‖ĝ_y‖_2 ≤ ‖f̂‖_2 = ‖f‖_2; inverting, g_y ∈ L² — consistent with ($\ast$).)*

### (c) g_y → f in L² as y → 0

By Plancherel applied to g_y − f, and ĝ_y − f̂ = (m_y − 1) f̂,

$$\|g_y - f\|_2^2 = \|\widehat{g_y} - \widehat{f}\|_2^2 = \int_{\mathbb{R}} \big| e^{-2\pi y|\xi|} - 1 \big|^2\, |\widehat{f}(\xi)|^2 \, d\xi.$$

Examine the integrand as y → 0⁺:

- **Pointwise limit**: for each fixed ξ, e^{-2π y|ξ|} → 1, so |e^{-2π y|ξ|} − 1|² |f̂(ξ)|² → 0.
- **Domination**: since 0 < e^{-2π y|ξ|} ≤ 1, we have |e^{-2π y|ξ|} − 1| ≤ 1, so the integrand is bounded by |f̂(ξ)|², which lies in L¹(ℝ) (as ‖f̂‖_2² = ‖f‖_2² < ∞) and is independent of y.

By the **dominated convergence theorem**,

$$\lim_{y \to 0} \|g_y - f\|_2^2 = \int_{\mathbb{R}} \lim_{y \to 0}\big| e^{-2\pi y|\xi|} - 1 \big|^2 |\widehat f(\xi)|^2\, d\xi = 0.$$

Hence g_y → f in L²(ℝ) as y → 0. ∎

## What Connects

**Within analysis**: g_y(x) is the value at (x, y) of the **harmonic extension** of f to the upper half-plane (P_y solves the Dirichlet problem there), and (c) is the statement that the boundary values are recovered in L². The family {P_y} is the prototypical **approximate identity**: nonnegative, total mass 1, concentrating at 0 — and (c) is the L² approximate-identity theorem, here proved cleanly on the Fourier side rather than by splitting the convolution into "near" and "far" pieces.

**The reusable principle**: a convolution operator is a **Fourier multiplier**, and its L²-theory is read directly off the multiplier — boundedness ⟺ the multiplier is bounded (here sup |m_y| = 1), and convergence of the family ⟺ pointwise convergence of the multipliers under an L¹ domination on |f̂|². The same template governs the heat semigroup (m_y(ξ) = e^{-4π² y|ξ|²}), Abel/Gauss summation, and mollifier families generally.

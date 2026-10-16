<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98A01: Dilation family $k^{\alpha} f(k|x|)$ — thresholds for uniform, a.e., and $L^{1}$ convergence

## Why It's Hard

The family $F_k(x) = k^{\alpha} f(k|x|)$ is a **concentrating dilation**: as $k \to \infty$ the profile $f(k|x|)$ squeezes toward the origin while the prefactor $k^{\alpha}$ inflates or deflates it. The three convergence modes probe completely different features of this competition, so they have **three different thresholds** — and the $L^{1}$ threshold even depends on the dimension $n$, with a regime where the functions are *not integrable at all*. What makes the bookkeeping work is that $f$ is pinned at **both ends**:

- $f(t)/t \to 1$ as $t \to 0$  $\Longrightarrow$  $f(t) \approx t$ near 0 (so $f(0) = 0$ and $f$ is small near the origin);
- $t^{4} f(t) \to 1$ as $t \to \infty$  $\Longrightarrow$  $f(t) \approx t^{-4}$ at infinity (polynomial decay).

Each mode reads off a *different* one of these facts: uniform convergence sees the global maximum, a.e. convergence sees the $t^{-4}$ tail (because $k|x| \to \infty$ for fixed $x \neq 0$), and $L^{1}$ convergence sees both ends through an integral whose finiteness hinges on the tail vs. the dimension.

Throughout, write $r = |x|$, and note $f$ is continuous and positive on $(0,\infty)$ with $f \to 0$ at both 0 and $\infty$, so $M := \sup_{t \geq 0} f(t)$ is a finite positive number, attained.

## The Key Insight

- **Uniform**: $\sup_x f(k|x|)$ is *scale-invariant* — as $|x|$ ranges over $[0,\infty)$ so does $k|x|$ — so $\|F_k\|_\infty = M \cdot k^{\alpha}$, and only the sign of $\alpha$ matters.
- **A.e.**: for *fixed* $x \neq 0$, $k|x| \to \infty$, so the $t^{4}f(t) \to 1$ asymptotic gives $F_k(x) \approx k^{\alpha-4}|x|^{-4}$; the exponent $\alpha - 4$ decides the pointwise limit.
- **$L^{1}$**: the substitution $s = k|x|$ turns the radial integral into $\|F_k\|_{1} = c_n k^{\alpha-n} \cdot \int_{0}^{\infty} f(s)s^{n-1}ds$, decoupling the $k$-power (exponent $\alpha - n$) from a fixed integral whose convergence at $\infty$ needs the $s^{-4}$ tail to beat $s^{n-1}$, i.e. $n \leq 3$.

## Complete Proof

**Answer.**

| mode | condition for $F_k \to 0$ |
|------|------------------------|
| (a) uniform | $\alpha < 0$ (every $n$) |
| (b) a.e. | $\alpha < 4$ (every $n$) |
| (c) $L^{1}(\mathbb{R}^{n})$ | $\alpha < n$ if $n \leq 3$; **no $\alpha$** if $n \geq 4$ (then $F_k \notin L^{1}$) |

### (a) Uniform convergence

For each fixed $k > 0$, as $x$ ranges over $\mathbb{R}^{n}$ the argument $k|x|$ ranges over all of $[0,\infty)$, so

$$\|F_k\|_\infty = \sup_{x \in \mathbb{R}^n} k^\alpha f(k|x|) = k^\alpha \sup_{s \geq 0} f(s) = M\,k^\alpha .$$

Since $0 < M < \infty$, we have $\|F_k\|_\infty \to 0$ iff $k^{\alpha} \to 0$ iff **$\alpha < 0$**. (At $\alpha = 0$, $\|F_k\|_\infty = M > 0$ for all $k$; at $\alpha > 0$ it diverges.)

### (b) Almost-everywhere convergence

At $x = 0$ (a single point, hence negligible), $F_k(0) = k^{\alpha} f(0) = 0$.

Fix $x \neq 0$, so $r = |x| > 0$ and $k r \to \infty$ as $k \to \infty$. From $t^{4} f(t) \to 1$ we may write $f(kr) = (kr)^{-4}(1 + o(1))$ as $k \to \infty$, hence

$$F_k(x) = k^\alpha f(kr) = k^\alpha (kr)^{-4}(1 + o(1)) = k^{\alpha - 4}\, r^{-4}(1 + o(1)).$$

For fixed $r > 0$ this tends to 0 iff $\alpha - 4 < 0$; if $\alpha = 4$ it tends to $r^{-4} \neq 0$, and if $\alpha > 4$ it diverges. So $F_k(x) \to 0$ for every $x \neq 0$ iff $\alpha < 4$, and the exceptional point $x = 0$ already gives 0. Therefore

- $\alpha < 4$: $F_k \to 0$ everywhere, in particular **a.e.**;
- $\alpha = 4$: $F_k \to r^{-4} \neq 0$ for a.e. $x$, so it does **not** converge to 0 a.e.;
- $\alpha > 4$: $F_k$ diverges a.e.

Hence (b) holds iff **$\alpha < 4$**.

### (c) $L^{1}$ convergence

All quantities are nonnegative, so Tonelli justifies the computation. Writing the integral in polar coordinates with $c_n = |S^{n-1}|$ the surface area of the unit sphere, and substituting $s = k r$ ($r = s/k$, $dr = ds/k$):

$$
\|F_k\|_{1} = \int_{\mathbb{R}^n} k^\alpha f(k|x|)\,dx
 = c_n \int_0^\infty k^\alpha f(kr)\, r^{n-1}\,dr
 = c_n\, k^{\alpha} \int_0^\infty f(s)\Big(\tfrac{s}{k}\Big)^{n-1}\tfrac{ds}{k}
 = c_n\, k^{\alpha - n} \underbrace{\int_0^\infty f(s)\, s^{n-1}\,ds}_{=: \,I_n}.
$$

So **$\|F_k\|_{1} = c_n k^{\alpha-n} I_n$**, with the $k$-dependence isolated in the power $\alpha - n$ and $I_n$ independent of $k$.

**Finiteness of $I_n$.** The integrand $g(s) = f(s) s^{n-1}$ is continuous and positive on $(0,\infty)$; convergence of $I_n$ is decided at the two ends:

- **near 0**: $f(s) \approx s$, so $g(s) \approx s^{n}$, and $\int_0 s^{n}\,ds$ converges for every $n \geq 1$;
- **at $\infty$**: $f(s) \approx s^{-4}$, so $g(s) \approx s^{n-5}$, and $\int^\infty s^{n-5}\,ds$ converges iff $n - 5 < -1$, i.e. **$n \leq 3$**.

Thus $I_n$ is finite (and positive) iff $n \in \{1, 2, 3\}$, and $I_n = +\infty$ for $n \geq 4$.

**Conclusion for (c).**

- If **$n \leq 3$**: $I_n \in (0, \infty)$ is a fixed constant, so $\|F_k\|_{1} = (c_n I_n)\,k^{\alpha-n} \to 0$ iff $\alpha - n < 0$, i.e. **$\alpha < n$**. (At $\alpha = n$ the norm is a positive constant; at $\alpha > n$ it diverges.)
- If **$n \geq 4$**: for *every* $k$ the integral $\int_{0}^{\infty} f(kr) r^{n-1} dr$ diverges (same $s^{n-5}$ tail), so $\|F_k\|_{1} = \infty$ — the functions $F_k$ are **not in $L^{1}(\mathbb{R}^{n})$ at all**, and "$F_k \to 0$ in $L^{1}$" holds for **no** value of $\alpha$.

$\blacksquare$

## What Connects

**Within analysis**: This is the standard "approximate-identity vs. spreading" dichotomy for dilations $g_k(x) = k^{\alpha} g(k x)$. The three thresholds (0, 4, and $n$) are the signatures of three norms scaling differently under dilation on $\mathbb{R}^{n}$: $L^{\infty}$ is scale-invariant in the profile (only $k^{\alpha}$ survives), pointwise values follow the decay exponent at $\infty$, and the $L^{1}$ mass scales like $k^{\alpha-n}$ because $dx$ carries $n$ powers of the dilation. The $n \geq 4$ obstruction is the familiar fact that a $t^{-4}$ radial tail is $L^{1}$ near $\infty$ only below dimension 4 ($s^{n-1} \cdot s^{-4}$ integrable $\iff$ $n < 4$).

**The reusable move**: when a quantity is a dilation $k^{\alpha} g(k \cdot)$, push the dilation onto the variable ($s = k|x|$) to separate a clean power $k^{\alpha - (\text{norm's homogeneity})}$ from a fixed, scale-free integral; finiteness of that integral is then a pure two-ends asymptotics question. The same computation underlies why $\delta$-sequences, heat kernels, and Sobolev-critical bubbles have the exponents they do.

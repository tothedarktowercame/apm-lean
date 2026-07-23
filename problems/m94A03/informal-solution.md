<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94A03: Is log|x| in H¹? — the borderline Sobolev function and its critical dimension

## Why It's Hard

`f(x) = \log|x|` blows up to `-\infty` at the origin, so naively it looks like it should fail
to be in any nice space. The subtlety is that Sobolev membership in `\mathbb{R}^n` is governed
by a competition between the strength of the singularity and the **dimension**: the volume
element `r^{n-1}\,dr` in polar coordinates suppresses singularities more strongly as `n` grows,
so whether `\log|x|` and its gradient are square-integrable depends entirely on `n`. The answer
is different for `n=2`, `n=3`, `n=4`, and getting it right means tracking the exponent in a
radial integral, not reasoning about the pointwise blow-up.

There is also a genuine technical trap: the *classical* gradient `x/|x|^2` is only defined away
from the origin, and one must check that it is the **weak** (distributional) gradient — that no
Dirac mass is hidden at the singular point. This requires an integration-by-parts argument whose
boundary term must be shown to vanish, and it is exactly the kind of step that is easy to skip.

## The Key Insight

In polar coordinates everything reduces to one-variable integrals `\int_0^1 r^{a}\,dr`, which
converge **iff `a > -1`**. Two such integrals decide membership:

- `\|f\|_{L^2}^2 = \omega_{n-1}\int_0^1 (\log r)^2\, r^{n-1}\,dr` — converges for *every* `n\ge 1`,
  because `r^{n-1}` (with `n-1\ge 0 > -1`) crushes the slow logarithmic growth. So the function
  part is **never** the obstruction.
- `\|\nabla f\|_{L^2}^2 = \omega_{n-1}\int_0^1 \frac{1}{r^2}\, r^{n-1}\,dr = \omega_{n-1}\int_0^1 r^{n-3}\,dr`
  — converges **iff `n-3 > -1`, i.e. `n > 2`**, because `|\nabla \log|x|| = 1/|x|`.

So the whole question is the single threshold `n > 2`. The gradient is the decisive term, and
`\log|x|` is the canonical *borderline* example: it just barely fails in `n=2` and just barely
succeeds in `n=3,4`. (Conceptually this is why `H^1(\mathbb{R}^2)` does **not** embed into
`L^\infty` — there are unbounded `H^1` functions — and `\log|x|` sits exactly at that edge.)

## Complete Proof

Let `\Omega = B(0,1) \subset \mathbb{R}^n`, `f(x) = \log|x|`, `r = |x|`. Write `dx = \omega_{n-1}\,r^{n-1}\,dr`
on radial integrands, where `\omega_{n-1} = |S^{n-1}|`. Recall `H^1(\Omega) = \{u \in L^2(\Omega): \nabla u \in L^2(\Omega)\}`,
the weak gradient.

**Step 0 — The function part is always fine.** For every `n \ge 1`,

$$\|f\|_{L^2(\Omega)}^2 = \omega_{n-1}\int_0^1 (\log r)^2\, r^{n-1}\,dr < \infty,$$

since the integrand is `r^{n-1}(\log r)^2` with `n-1 \ge 0 > -1` (the integral `\int_0^1 r^a(\log r)^2 dr`
converges for all `a > -1`; e.g. it is finite even at `n=1`, equal to `2`). So `f \in L^2(\Omega)`
in every dimension, and membership in `H^1` will be decided solely by the gradient.

**Step 1 — The weak gradient is `x/|x|^2`, with `|\nabla f| = 1/r`.** Away from `0`, classical
differentiation gives `\nabla \log|x| = \dfrac{x}{|x|^2}`, so `|\nabla f| = \dfrac{|x|}{|x|^2} = \dfrac1r`.
This candidate is in `L^1_{loc}(\Omega)` precisely when `\int_0^1 r^{-1}\, r^{n-1}\,dr = \int_0^1 r^{n-2}\,dr < \infty`,
i.e. for `n \ge 2`. For such `n` we verify it is the weak gradient: for `\varphi \in C_c^\infty(\Omega)`,
integrate by parts on `\Omega \setminus B(0,\varepsilon)`,

$$\int_{\Omega\setminus B(0,\varepsilon)} f\, \partial_i \varphi \,dx
= -\int_{\Omega\setminus B(0,\varepsilon)} (\partial_i f)\,\varphi\,dx
+ \int_{\partial B(0,\varepsilon)} f\,\varphi\, \nu_i \,dS.$$

The boundary term over the sphere `r=\varepsilon` is bounded by

$$\Big|\int_{\partial B(0,\varepsilon)} f\varphi\,\nu_i\,dS\Big|
\le \|\varphi\|_\infty\, |\log \varepsilon|\, \cdot \omega_{n-1}\varepsilon^{n-1}
= C\,\varepsilon^{n-1}|\log\varepsilon| \xrightarrow[\varepsilon\to0]{} 0 \quad (n \ge 2),$$

since `\varepsilon^{n-1}|\log\varepsilon|\to 0` for `n-1 \ge 1`. Letting `\varepsilon \to 0` gives
`\int_\Omega f\,\partial_i\varphi = -\int_\Omega (x_i/|x|^2)\varphi`, so `x/|x|^2` is indeed the
weak gradient (no Dirac mass appears). Thus for `n\ge 2`, `\nabla f = x/|x|^2` weakly.

**Step 2 — Square-integrability of the gradient.** For `n \ge 2`,

$$\|\nabla f\|_{L^2(\Omega)}^2 = \int_\Omega \frac{1}{|x|^2}\,dx
= \omega_{n-1}\int_0^1 \frac{1}{r^2}\, r^{n-1}\,dr = \omega_{n-1}\int_0^1 r^{\,n-3}\,dr,$$

which converges **iff `n - 3 > -1`, i.e. `n > 2`**.

**Step 3 — Answers by dimension.**

- **`n = 2`:** `\displaystyle\int_0^1 r^{-1}\,dr = \lim_{\varepsilon\to0}[\log r]_\varepsilon^1 = +\infty`.
  So `\nabla f \notin L^2(\Omega)`, and although `f \in L^2(\Omega)`,

$$\boxed{\ f = \log|x| \notin H^1(\Omega)\ \text{when } n = 2.\ }$$

- **`n = 3`:** `\displaystyle\int_0^1 r^{0}\,dr = 1 < \infty`, so `\nabla f \in L^2(\Omega)` and

$$\boxed{\ f = \log|x| \in H^1(\Omega)\ \text{when } n = 3.\ }$$

- **`n = 4`:** `\displaystyle\int_0^1 r^{1}\,dr = \tfrac12 < \infty`, so `\nabla f \in L^2(\Omega)` and

$$\boxed{\ f = \log|x| \in H^1(\Omega)\ \text{when } n = 4.\ }$$

**Conclusion.** `\log|x| \in H^1(B(0,1))` if and only if `n \ge 3`. The function is square-integrable
in every dimension; it is the gradient `1/|x|` whose `L^2`-norm `\int_0^1 r^{n-3}dr` decides
everything, with the critical dimension at `n = 2`. This makes `\log|x|` the textbook witness that
`H^1` functions can be **unbounded** for `n \ge 3` (it has a `-\infty` singularity at the origin yet
belongs to `H^1`), and that the Sobolev embedding `H^1 \hookrightarrow L^\infty` fails exactly from
`n = 2` upward. ∎

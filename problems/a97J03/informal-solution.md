<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J03: Convolution of L^p and L^q functions lies in C₀

## Why It's Hard

The problem packages **two genuinely different analytic facts** behind one innocent-looking convolution integral $h = f * g$, and neither follows by "pass the limit inside the integral."

- **Continuity** cannot be obtained by dominated convergence in any naive way, because there is no single integrable dominating function uniform in $y$. The right tool is **continuity of translation in $L^p$** — the statement that $y \mapsto \tau_y f$ is a continuous map $\mathbb{R} \to L^p$ — which is itself a nontrivial density theorem, not an elementary computation.
- **Vanishing at infinity** is *false* pointwise for individual integrands; it only emerges after a **$C_c$-density / uniform-approximation** argument. You approximate $f, g$ by compactly supported continuous functions, observe that *their* convolution has compact support, and then transfer "vanishes at infinity" across a uniform limit.

The glue holding both halves together is a single Hölder estimate, and the whole result depends crucially on $1 < p, q < \infty$ being **finite conjugate exponents**: finiteness is exactly what makes $C_c$ dense and translation continuous. The analogous statement fails at the endpoints (e.g. for $L^\infty$).

## The Key Insight

Hölder's inequality with the conjugate pair $(p,q)$ gives, for *every* $y$,
$$|h(y)| \le \int |f(y-x)|\,|g(x)|\,dm(x) \le \|f\|_p\,\|g\|_q,$$
so convolution is a **bounded bilinear map into $L^\infty$**: $\|f*g\|_\infty \le \|f\|_p\|g\|_q$.

This one estimate does double duty.

1. Rewriting $h(y) = \langle \tau_y \check f,\, g\rangle$ (a pairing of a *translate* of $f$ against $g$), the same Hölder bound applied to a difference converts $L^p$-continuity of translation directly into continuity of $h$.
2. Applied to differences again, it controls the error when $f,g$ are replaced by $C_c$ approximants — so $h$ is a *uniform* limit of compactly supported convolutions, each of which trivially vanishes outside a bounded set.

Recognize this as the structural fact $h \in C_0(\mathbb{R})$, the space of continuous functions vanishing at infinity.

## Complete Proof

Throughout, $m$ is Lebesgue measure, $\tau_y f(x) := f(x-y)$ is translation, and $\check f(x) := f(-x)$ is reflection. Both operations preserve every $L^r$ norm, since $m$ is translation- and reflection-invariant.

### Step 0 — $h$ is well-defined and uniformly bounded

Fix $y \in \mathbb{R}$. The function $x \mapsto f(y-x)$ has the same $L^p$ norm as $f$ (it is a reflected translate), and $g \in L^q$ with $1/p + 1/q = 1$. By **Hölder's inequality**,
$$\int_{-\infty}^{\infty} |f(y-x)|\,|g(x)|\,dm(x) \le \Big(\int |f(y-x)|^p\,dm\Big)^{1/p}\Big(\int |g|^q\,dm\Big)^{1/q} = \|f\|_p\,\|g\|_q < \infty.$$
Hence the defining integral converges absolutely for every $y$, $h$ is everywhere defined, and
$$\|h\|_\infty \le \|f\|_p\,\|g\|_q. \tag{$\ast$}$$
Note $(\ast)$ is *bilinear*: for any $u \in L^p$, $v \in L^q$ the same argument gives $\|u*v\|_\infty \le \|u\|_p\|v\|_q$. We use this repeatedly below on differences.

### Step 1 — $h$ is (uniformly) continuous

Recast $h$ as a pairing. Since $f(y-x) = f(-(x-y)) = \check f(x-y) = (\tau_y \check f)(x)$,
$$h(y) = \int (\tau_y \check f)(x)\, g(x)\, dm(x).$$
For any $y, y' \in \mathbb{R}$, linearity of the integral and Hölder give
$$|h(y) - h(y')| = \left| \int \big[\tau_y \check f - \tau_{y'} \check f\big](x)\, g(x)\, dm(x)\right| \le \big\|\tau_y \check f - \tau_{y'} \check f\big\|_p\;\|g\|_q.$$
By translation invariance of the norm, $\big\|\tau_y \check f - \tau_{y'}\check f\big\|_p = \big\|\tau_{y-y'}\check f - \check f\big\|_p$, so
$$|h(y) - h(y')| \le \big\|\tau_{y-y'}\check f - \check f\big\|_p\;\|g\|_q. \tag{$\dagger$}$$

Now invoke **continuity of translation in $L^p$** (valid for $1 \le p < \infty$): for every $\varphi \in L^p$,
$$\lim_{t \to 0} \|\tau_t \varphi - \varphi\|_p = 0.$$
*(Proof sketch of this standard lemma: it holds for $\varphi \in C_c$ by uniform continuity and the dominated/compact-support estimate $\|\tau_t\varphi - \varphi\|_p^p \le (2\,\mathrm{len})\cdot \sup_{|x-x'|\le|t|}|\varphi(x)-\varphi(x')|^p \to 0$; then extend to all of $L^p$ by density of $C_c$ in $L^p$ and the uniform bound $\|\tau_t\varphi - \varphi\|_p \le 2\|\varphi\|_p$, via a $3\varepsilon$ argument.)*

Apply this to $\varphi = \check f \in L^p$. As $y' \to y$ we have $t := y - y' \to 0$, so the right side of $(\dagger)$ tends to $0$. Therefore $h$ is continuous at every $y$. In fact, because the bound in $(\dagger)$ depends only on the difference $y - y'$, $h$ is **uniformly continuous** on $\mathbb{R}$. $\checkmark$

### Step 2 — $\lim_{y \to \pm\infty} h(y) = 0$

We show $h$ is a uniform limit of compactly supported convolutions.

**(a) Compactly supported convolutions vanish at infinity.** Suppose $f_1, g_1 \in C_c(\mathbb{R})$ with $\operatorname{supp} f_1 \subseteq [-R,R]$ and $\operatorname{supp} g_1 \subseteq [-R,R]$. For the integrand of $(f_1 * g_1)(y) = \int f_1(y-x) g_1(x)\,dm(x)$ to be nonzero we need both $x \in [-R,R]$ and $y - x \in [-R,R]$, forcing $y \in [-2R, 2R]$. Hence
$$(f_1 * g_1)(y) = 0 \quad \text{whenever } |y| > 2R,$$
so in particular $\lim_{y\to\pm\infty}(f_1*g_1)(y) = 0$.

**(b) Uniform approximation.** Fix $\varepsilon > 0$. Because $1 < p, q < \infty$ are finite, $C_c(\mathbb{R})$ is **dense** in both $L^p$ and $L^q$. Choose $f_1, g_1 \in C_c(\mathbb{R})$ with
$$\|f - f_1\|_p < \varepsilon, \qquad \|g - g_1\|_q < \varepsilon.$$
Using bilinearity and the uniform bound $(\ast)$ on each difference:
$$
\begin{aligned}
\|h - f_1 * g_1\|_\infty
&= \big\|(f*g) - (f_1*g_1)\big\|_\infty \\
&\le \big\|(f - f_1)*g\big\|_\infty + \big\|f_1 *(g - g_1)\big\|_\infty \\
&\le \|f - f_1\|_p\,\|g\|_q \;+\; \|f_1\|_p\,\|g - g_1\|_q \\
&< \varepsilon\,\|g\|_q \;+\; (\|f\|_p + \varepsilon)\,\varepsilon,
\end{aligned}
$$
where we used $\|f_1\|_p \le \|f\|_p + \|f - f_1\|_p < \|f\|_p + \varepsilon$. The right-hand side is $\le \varepsilon\big(\|f\|_p + \|g\|_q + \varepsilon\big) =: \delta(\varepsilon)$, and $\delta(\varepsilon) \to 0$ as $\varepsilon \to 0$.

**(c) Transfer across the uniform limit.** Let $R$ be the support radius for the chosen $f_1, g_1$ as in (a). For any $|y| > 2R$ we have $(f_1*g_1)(y) = 0$, hence
$$|h(y)| = |h(y) - (f_1*g_1)(y)| \le \|h - f_1*g_1\|_\infty < \delta(\varepsilon).$$
Thus $\limsup_{|y|\to\infty} |h(y)| \le \delta(\varepsilon)$. Since $\varepsilon > 0$ was arbitrary and $\delta(\varepsilon) \to 0$,
$$\lim_{y \to \pm\infty} h(y) = 0. \qquad \blacksquare$$

### Conclusion

Combining Steps 1 and 2, $h = f * g$ is continuous on $\mathbb{R}$ and vanishes at $\pm\infty$; equivalently, $h \in C_0(\mathbb{R})$, with the quantitative envelope $\|h\|_\infty \le \|f\|_p\,\|g\|_q$.

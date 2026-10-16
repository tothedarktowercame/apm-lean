<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J02: Convolution of $L^{2}$ indicators is continuous, and the Steinhaus overlap estimate

## Why It's Hard

$\chi_E$ is, in general, **wildly discontinuous** — $E$ is an arbitrary positive-measure measurable subset of $[0,1]$, so $\chi_E$ can jump on a dense, fractal-like set. Yet the convolution $\chi_E \ast \chi_E$ is asserted to be *continuous*. The point is that convolution **regularizes**: integrating $\chi_E$ against a translate of itself averages out the pointwise pathology, and the right way to see this is not pointwise but through the **continuity of translation in $L^{2}$**, which holds for *every* $L^{2}$ function regardless of how badly it behaves pointwise.

Part (b) hides a second subtlety. We will know the overlap $|E \cap (E+t)|$ equals $|E| > 0$ *at the single point $t = 0$*; but "positive at one point" says nothing about a neighborhood unless the overlap is a **continuous** function of $t$. So (b) is exactly an application of the regularity proved in (a): continuity is what lets a single positive value spread to a whole interval.

Note $\chi_E \in L^{2}(\mathbb{R})$: it is bounded by 1 and supported in $[0,1]$, so $\int \chi_E^{2} = |E| \leq 1 < \infty$ (likewise $\chi_E \in L^{1}$).

## The Key Insight

One lemma does both parts:

> **Lemma.** If $f, g \in L^{2}(\mathbb{R})$, then $h(x) = \int f(x-y)g(y)\,dy$ is (uniformly) continuous.

The proof is Cauchy–Schwarz plus the standard fact that translation is continuous in $L^{2}$: $\Vert f(\cdot+\delta) - f\Vert_{2} \to 0$ as $\delta \to 0$. Then:

- **(a)** is the Lemma with $f = g = \chi_E$.
- **(b)**: the overlap $\phi(t) = |E \cap (E+t)| = \int \chi_E(y) \chi_E(y-t)\,dy$ is the same kind of integral (it is $\chi_E \ast \chi_{-E}$ evaluated at $t$), so the Lemma makes it continuous; since $\phi(0) = |E| > 0$, continuity keeps $\phi$ positive on a neighborhood of 0.

## Complete Proof

**Lemma.** Let $f, g \in L^{2}(\mathbb{R})$ and $h(x) = \int_{\mathbb{R}} f(x-y) g(y)\,dy$. Then $h$ is well-defined, bounded, and uniformly continuous.

*Proof.* For fixed $x$, the map $y \mapsto f(x-y)$ is in $L^{2}$ (translation/reflection preserve the $L^{2}$ norm), and $g \in L^{2}$, so by Cauchy–Schwarz the integrand is integrable and $|h(x)| \leq \Vert f\Vert_{2}\Vert g\Vert_{2}$; thus $h$ is well-defined and bounded. For the modulus of continuity, fix $\delta \in \mathbb{R}$ and estimate

$$
h(x+\delta) - h(x) = \int_{\mathbb R}\big[f(x+\delta - y) - f(x - y)\big]\,g(y)\,dy,
$$

so by Cauchy–Schwarz,

$$
|h(x+\delta) - h(x)| \;\leq\; \Big(\int_{\mathbb R} |f(x+\delta-y) - f(x-y)|^2\,dy\Big)^{1/2}\,\|g\|_2 .
$$

Substituting $u = x - y$ in the first factor (Lebesgue measure is translation-invariant),

$$
\int_{\mathbb R} |f(x+\delta-y) - f(x-y)|^2\,dy = \int_{\mathbb R} |f(u+\delta) - f(u)|^2\,du = \|f(\cdot+\delta) - f\|_2^2 .
$$

Hence, **uniformly in $x$**,

$$
|h(x+\delta) - h(x)| \;\leq\; \|f(\cdot+\delta) - f\|_2\,\|g\|_2 . \tag{$\ast$}
$$

It remains to recall **continuity of translation in $L^{2}$**: $\Vert f(\cdot+\delta) - f\Vert_{2} \to 0$ as $\delta \to 0$. (Given $\epsilon > 0$, pick $\phi \in C_c(\mathbb{R})$ with $\Vert f - \phi\Vert_{2} < \epsilon$, possible by density of $C_c$ in $L^{2}$; $\phi$ is uniformly continuous with compact support, so $\Vert \phi(\cdot+\delta) - \phi\Vert_{2} \to 0$ by dominated convergence; then $\Vert f(\cdot+\delta) - f\Vert_{2} \leq 2\Vert f - \phi\Vert_{2} + \Vert \phi(\cdot+\delta) - \phi\Vert_{2} < 3\epsilon$ for $\delta$ small.) By ($\ast$), $h$ is uniformly continuous. ∎

**(a).** Since $\chi_E \in L^{2}(\mathbb{R})$, the Lemma with $f = g = \chi_E$ shows

$$
\chi_E \ast \chi_E (x) = \int_{\mathbb R} \chi_E(x-y)\,\chi_E(y)\,dy
$$

is (uniformly) continuous in $x$. ∎

**(b).** For $t \in \mathbb{R}$, the translate satisfies $\chi_{E+t}(y) = \chi_E(y - t)$, so

$$
|E \cap (E+t)| = \int_{\mathbb R} \chi_E(y)\,\chi_{E+t}(y)\,dy = \int_{\mathbb R} \chi_E(y)\,\chi_E(y-t)\,dy =: \varphi(t).
$$

This is exactly an integral of the Lemma's form: with $\check{g}(y) := \chi_E(-y) = \chi_{-E}(y)$,

$$
\varphi(t) = \int_{\mathbb R} \chi_E(t - u)\,\chi_E(-u)\,du \quad (u = t - y) \;=\; (\chi_E \ast \chi_{-E})(t),
$$

a convolution of the two $L^{2}$ functions $\chi_E$ and $\chi_{-E}$. By the Lemma, **$\phi$ is continuous on $\mathbb{R}$**. At $t = 0$,

$$
\varphi(0) = \int_{\mathbb R}\chi_E(y)^2\,dy = |E| > 0 .
$$

By continuity at 0 applied with the value $|E|/2 > 0$: there exists $\epsilon > 0$ such that $|\phi(t) - \phi(0)| < |E|/2$ whenever $|t| < \epsilon$, and hence

$$
|E \cap (E+t)| = \varphi(t) > \varphi(0) - \tfrac{|E|}{2} = \tfrac{|E|}{2} > 0 \qquad \text{for all } |t| < \varepsilon . \qquad \blacksquare
$$

## What Connects

**Within analysis**: This is the engine of the **Steinhaus theorem** — that the difference set $E - E$ contains an open interval around 0 when $|E| > 0$. Indeed $|E \cap (E+t)| > 0$ forces $E \cap (E+t) \neq \emptyset$, i.e. $t \in E - E$; so part (b) says $(-\epsilon, \epsilon) \subseteq E - E$. The proof needs no special structure on $E$, only positive measure, which is why it is a workhorse for "measurable $\Longrightarrow$ a little bit of regularity" results (e.g. measurable additive functions are linear, measurable subgroups of $\mathbb{R}$ are open).

**The reusable principle**: convolution turns $L^{2}$ (or $L^{1}$) data into a continuous function — the autocorrelation of any $L^{2}$ function is continuous — and Cauchy–Schwarz reduces the whole matter to continuity of translation in $L^p$ ($1 \leq p < \infty$), itself a density-of-$C_c$ argument. The same ($\ast$)-estimate proves that $f \ast g$ is continuous whenever the exponents are conjugate (Hölder in place of Cauchy–Schwarz).

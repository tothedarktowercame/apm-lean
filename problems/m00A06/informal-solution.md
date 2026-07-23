<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m00A06: Regularizing the non-integrable 1/|x| into a distribution

## Why It's Hard

The function $1/|x|$ is *locally non-integrable* at the origin — $\int_{-\delta}^{\delta}
|x|^{-1}\,dx$ diverges logarithmically — so the naive pairing $T_f(\varphi)=\int|x|^{-1}
\varphi$ does **not** define a distribution: it is infinite on any test function with
$\varphi(0)\neq0$. The task is to see exactly where the obstruction lives (only at the
single point $0$, and only through the value $\varphi(0)$) and to surgically remove it.
The cure is a *finite-part* regularization: subtract $\varphi(0)$ near $0$, which supplies
a vanishing factor $\sim|x|$ that exactly cancels the $|x|^{-1}$ singularity, leaving a
genuine, continuous linear functional that still agrees with the honest integral whenever
that integral converges.

## The Key Insight

- **(a)** If $\varphi(0)\neq0$ then near $0$, $|x|^{-1}\varphi(x)\sim\varphi(0)|x|^{-1}$,
  and $\int_{|x|<\delta}|x|^{-1}\,dx=+\infty$.
- **(b)** If $\varphi(0)=0$ then $|\varphi(x)|\le\|\varphi'\|_\infty|x|$, so
  $|x|^{-1}|\varphi(x)|\le\|\varphi'\|_\infty$ is bounded — integrable on the compact
  support.
- **(c)** Define $\displaystyle T(\varphi)=\int_{|x|\le1}\frac{\varphi(x)-\varphi(0)}{|x|}\,dx
  +\int_{|x|>1}\frac{\varphi(x)}{|x|}\,dx$. The subtraction tames the singularity, $T$ is a
  distribution, and $T=T_f$ when $\varphi(0)=0$.

## Complete Proof

Here $\mathcal D=C_c^\infty(\mathbb R)$ are the test functions and $\mathcal D'$ the
distributions; $T_f(\varphi)=\int_{-\infty}^\infty|x|^{-1}\varphi(x)\,dx$.

### (a) $T_f$ is not well-defined on all of $\mathcal D$

Choose $\varphi\in\mathcal D$ with $\varphi\ge0$ and $\varphi\equiv1$ on $[-1,1]$ (a
standard bump). Then on $[-1,1]$ the integrand is $|x|^{-1}\varphi(x)=|x|^{-1}\ge0$, so
$$
\int_{-\infty}^{\infty}|x|^{-1}\varphi(x)\,dx\ \ge\ \int_{-1}^{1}|x|^{-1}\,dx
=2\int_0^1\frac{dx}{x}=2\lim_{\varepsilon\to0^+}\big(-\ln\varepsilon\big)=+\infty .
$$
The defining integral diverges, so $T_f(\varphi)$ is not defined for this $\varphi$.
(More generally it diverges whenever $\varphi(0)\neq0$: near $0$, $|x|^{-1}\varphi(x)$ has
constant sign and magnitude $\sim|\varphi(0)|\,|x|^{-1}$, whose integral is infinite.)
$\quad\checkmark$

### (b) $T_f$ is defined for $\varphi\in\mathcal D$ with $\varphi(0)=0$

Let $\varphi\in\mathcal D$ with $\varphi(0)=0$, and let $\operatorname{supp}\varphi\subseteq
[-R,R]$. By the fundamental theorem of calculus, for every $x$,
$$
|\varphi(x)|=\Big|\int_0^x\varphi'(t)\,dt\Big|\le\|\varphi'\|_\infty\,|x| .
$$
Hence the integrand is bounded:
$$
\big|\,|x|^{-1}\varphi(x)\,\big|\le\|\varphi'\|_\infty\quad\text{for }0<|x|\le R,
$$
and it vanishes for $|x|>R$. Therefore
$$
\int_{-\infty}^\infty\big|\,|x|^{-1}\varphi(x)\,\big|\,dx\le \|\varphi'\|_\infty\cdot 2R<\infty,
$$
so $T_f(\varphi)$ is a well-defined (absolutely convergent) integral. $\quad\checkmark$

### (c) A distribution $T\in\mathcal D'$ agreeing with $T_f$ where $\varphi(0)=0$

Define, for $\varphi\in\mathcal D$,
$$
T(\varphi)=\int_{|x|\le1}\frac{\varphi(x)-\varphi(0)}{|x|}\,dx+\int_{|x|>1}\frac{\varphi(x)}{|x|}\,dx .
$$

**$T$ is well-defined (finite) on all of $\mathcal D$.** On $|x|\le1$, the FTC bound gives
$|\varphi(x)-\varphi(0)|\le\|\varphi'\|_\infty|x|$, so the first integrand is bounded by
$\|\varphi'\|_\infty$ and the integral converges. On $|x|>1$, $|x|^{-1}\le1$ and $\varphi$
has compact support, so the second integral converges. Thus $T(\varphi)\in\mathbb R$ for
every $\varphi$.

**$T$ is linear** in $\varphi$ (both integrals are linear, and $\varphi\mapsto\varphi(0)$
is linear).

**$T$ is continuous, i.e. $T\in\mathcal D'$.** Fix a compact $K$ and let $\varphi\in
\mathcal D$ with $\operatorname{supp}\varphi\subseteq K\subseteq[-R,R]$. Then
$$
|T(\varphi)|\le\int_{|x|\le1}\frac{|\varphi(x)-\varphi(0)|}{|x|}\,dx+\int_{1<|x|\le R}\frac{|\varphi(x)|}{|x|}\,dx
\le 2\,\|\varphi'\|_\infty+2R\,\|\varphi\|_\infty .
$$
So $|T(\varphi)|\le C_K\big(\sup|\varphi|+\sup|\varphi'|\big)$, a bound by finitely many
seminorms uniformly over test functions supported in $K$. Hence $T$ is continuous on
$\mathcal D$ (indeed of order $\le1$), so $T\in\mathcal D'$.

**$T$ agrees with $T_f$ when $\varphi(0)=0$.** If $\varphi(0)=0$, the subtraction does
nothing, and
$$
T(\varphi)=\int_{|x|\le1}\frac{\varphi(x)}{|x|}\,dx+\int_{|x|>1}\frac{\varphi(x)}{|x|}\,dx
=\int_{-\infty}^{\infty}\frac{\varphi(x)}{|x|}\,dx=T_f(\varphi),
$$
the middle integral being absolutely convergent by part (b). $\quad\blacksquare$

### Remark

$T$ is the **finite-part (Hadamard) regularization** of $|x|^{-1}$, often written
$\operatorname{Pf}\,|x|^{-1}$. The construction is the model for regularizing any
homogeneous singularity: subtract the Taylor obstruction (here just $\varphi(0)$, since
$|x|^{-1}$ has a "$\log$"-borderline singularity needing one subtraction) on a neighborhood
of the bad point. The extension is **not unique** — any $T+c\,\delta_0$ (and, with a
different cutoff radius, $T+c'\delta_0$) also agrees with $T_f$ off the origin — reflecting
that distributions supported at $\{0\}$ are the ambiguity, exactly the freedom in choosing
"how much of the divergence to discard."

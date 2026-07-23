<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99J03: Three distributional limits — a nascent delta, a dipole $\to\delta'$, and a dilation $\to$ constant

## Why It's Hard

Convergence in $\mathcal D'(\mathbb R)$ is **weak-$*$**: $\ell_{g_n}\to T$ means $\int g_n\varphi\to T(\varphi)$ for *every* test function $\varphi\in C_c^\infty$. The trap is that the **pointwise** behavior of $g_n$ is wildly misleading:

- **(a)** $g_n$ is a spike of height $n\to\infty$ at the origin — pointwise it diverges at $0$ and is $0$ elsewhere, which is "nonsense" as a function, yet as a distribution it converges to something perfectly definite. The content is recognizing the **area is exactly $1$**, making it an approximate identity (nascent delta).
- **(b)** is the genuinely subtle one: a positive block immediately followed by a negative block of height $n^2$. The leading (zeroth-order) contributions **cancel**, so the limit is determined by the **first moment** — one must Taylor expand $\varphi$ to order one and watch the $n^2$ scaling conspire with the $1/n^2$ first moment to leave $-\varphi'(0)$. Stopping at "the masses cancel, limit $0$" is the standard error; the answer is $\delta'$, not $0$.
- **(c)** $g_n(x)=\psi(x/n)$ does the opposite of concentrating — it **dilates** $\psi$ out to infinity, flattening it toward the constant $\psi(0)$. The difficulty is justifying the passage to the limit inside the integral (dominated convergence on the compact support of $\varphi$).

So all three converge, but to three structurally different objects — $\delta$, $\delta'$, and a constant — and each requires reading the weak-$*$ limit, not the pointwise one.

## The Key Insight

Test against $\varphi\in C_c^\infty$ and Taylor-expand at the point of concentration:

- **(a)** $g_n\ge0$ with $\int g_n=1$ (triangle of base $2/n$, height $n$). Then $\int g_n\varphi-\varphi(0)=\int g_n(\varphi-\varphi(0))\to0$ since $\varphi$ is continuous and $g_n$ concentrates at $0$. **Limit $=\delta$.**
- **(b)** Equal $\pm$ masses straddling $0$: writing $\varphi(x)=\varphi(0)+\varphi'(0)x+O(x^2)$, the $\varphi(0)$ terms cancel and the surviving first-moment term gives $\int g_n\varphi\to-\varphi'(0)$. **Limit $=\delta'$** (since $\langle\delta',\varphi\rangle=-\varphi'(0)$).
- **(c)** $\psi(x/n)\to\psi(0)$ uniformly on $\operatorname{supp}\varphi$, so $\int\psi(x/n)\varphi\to\psi(0)\int\varphi$. **Limit $=\psi(0)\cdot\mathbf 1$**, the constant distribution.

The three model the three basic moves of approximate-identity theory: **concentrate** (→$\delta$), **concentrate with a sign flip** (→$\delta'$), and **spread out** (→ constant).

## Complete Proof

A sequence $\ell_{g_n}\in\mathcal D'(\mathbb R)$ converges to $T$ iff $\ell_{g_n}(\varphi)=\int_{-\infty}^\infty g_n(x)\varphi(x)\,dx\to T(\varphi)$ for every $\varphi\in C_c^\infty(\mathbb R)$. Fix such a $\varphi$, and let $R>0$ be such that $\operatorname{supp}\varphi\subseteq[-R,R]$; write $M_k=\sup|\varphi^{(k)}|<\infty$.

### Part (a): the triangular spike $\to\delta$

Here $g_n(x)=n\big(1-n|x|\big)$ for $|x|\le 1/n$ and $0$ otherwise: a nonnegative triangle of height $n$ on the base $[-1/n,1/n]$. Its total mass is
$$
\int_{-\infty}^\infty g_n(x)\,dx=\tfrac12\cdot\underbrace{\tfrac2n}_{\text{base}}\cdot\underbrace{n}_{\text{height}}=1 .
$$
Using this normalization,
$$
\ell_{g_n}(\varphi)-\varphi(0)=\int_{-1/n}^{1/n}g_n(x)\big[\varphi(x)-\varphi(0)\big]\,dx .
$$
Since $g_n\ge0$ and $g_n$ is supported in $|x|\le1/n$,
$$
\big|\ell_{g_n}(\varphi)-\varphi(0)\big|\le\Big(\sup_{|x|\le1/n}|\varphi(x)-\varphi(0)|\Big)\int_{-1/n}^{1/n}g_n
=\sup_{|x|\le1/n}|\varphi(x)-\varphi(0)| .
$$
By continuity of $\varphi$ at $0$, the right side $\to0$ as $n\to\infty$ (explicitly $\le M_1/n$ by the mean value theorem). Hence
$$
\ell_{g_n}(\varphi)\to\varphi(0)=\langle\delta,\varphi\rangle\qquad\text{for all }\varphi,
$$
so the sequence **converges in $\mathcal D'$ to the Dirac delta**, $\ell_{g_n}\to\delta$. $\qquad\checkmark$

### Part (b): the dipole $\to\delta'$

Here $g_n(x)=n^2$ on $(-1/n,0)$, $g_n(x)=-n^2$ on $[0,1/n]$, and $0$ elsewhere, so
$$
\ell_{g_n}(\varphi)=n^2\left[\int_{-1/n}^{0}\varphi(x)\,dx-\int_{0}^{1/n}\varphi(x)\,dx\right].
$$
By Taylor's theorem with remainder, $\varphi(x)=\varphi(0)+\varphi'(0)x+\tfrac12\varphi''(\xi_x)x^2$ with $|\varphi''(\xi_x)|\le M_2$. Integrate each piece:
$$
\int_{-1/n}^{0}\varphi=\frac{\varphi(0)}{n}+\varphi'(0)\!\int_{-1/n}^0\!\! x\,dx+r_n^-
=\frac{\varphi(0)}{n}-\frac{\varphi'(0)}{2n^2}+r_n^-,
$$
$$
\int_{0}^{1/n}\varphi=\frac{\varphi(0)}{n}+\varphi'(0)\!\int_{0}^{1/n}\!\! x\,dx+r_n^+
=\frac{\varphi(0)}{n}+\frac{\varphi'(0)}{2n^2}+r_n^+,
$$
where the remainders satisfy $|r_n^\pm|\le\tfrac12 M_2\int_0^{1/n}x^2\,dx=\dfrac{M_2}{6n^3}$. Subtracting, the $\varphi(0)/n$ terms cancel:
$$
\int_{-1/n}^{0}\varphi-\int_{0}^{1/n}\varphi=-\frac{\varphi'(0)}{n^2}+\big(r_n^--r_n^+\big),\qquad |r_n^--r_n^+|\le\frac{M_2}{3n^3}.
$$
Multiplying by $n^2$,
$$
\ell_{g_n}(\varphi)=-\varphi'(0)+n^2\big(r_n^--r_n^+\big),\qquad \big|n^2(r_n^--r_n^+)\big|\le\frac{M_2}{3n}\to0 .
$$
Therefore
$$
\ell_{g_n}(\varphi)\to-\varphi'(0)=\langle\delta',\varphi\rangle\qquad\text{for all }\varphi,
$$
so the sequence **converges in $\mathcal D'$ to $\delta'$**, the distributional derivative of the Dirac delta. (The zeroth moments cancel by the sign flip; the *first* moment, scaled by $n^2$, is what survives.) $\qquad\checkmark$

### Part (c): the dilation $\to$ the constant $\psi(0)$

Here $g_n(x)=\psi(x/n)$ with $\psi\in C^\infty(\mathbb R)$. For $\varphi$ supported in $[-R,R]$,
$$
\ell_{g_n}(\varphi)=\int_{-R}^{R}\psi\!\big(\tfrac{x}{n}\big)\varphi(x)\,dx .
$$
For $x\in[-R,R]$ we have $x/n\in[-R,R]$, where $\psi$ is bounded, say $|\psi|\le M$; hence the integrand is dominated by $M|\varphi(x)|$, which is integrable. As $n\to\infty$, $x/n\to0$ and by continuity $\psi(x/n)\to\psi(0)$ pointwise, so $\psi(x/n)\varphi(x)\to\psi(0)\varphi(x)$. By the **dominated convergence theorem**,
$$
\ell_{g_n}(\varphi)\to\int_{-R}^{R}\psi(0)\varphi(x)\,dx=\psi(0)\int_{-\infty}^{\infty}\varphi(x)\,dx=\psi(0)\,\langle\mathbf 1,\varphi\rangle .
$$
(One may instead note $\psi(x/n)\to\psi(0)$ *uniformly* on $[-R,R]$, since $|\psi(x/n)-\psi(0)|\le \frac{R}{n}\sup_{[-R,R]}|\psi'|$, giving the same conclusion with an explicit $O(1/n)$ rate.) Therefore the sequence **converges in $\mathcal D'$ to the constant distribution** $\psi(0)\cdot\mathbf 1$ (the regular distribution induced by the constant function $\psi(0)$). $\qquad\blacksquare$

### Summary and Remark

| part | $g_n$ | limit in $\mathcal D'$ | $\ell_{g_n}(\varphi)\to$ |
|---|---|---|---|
| (a) | unit triangle, base $2/n$, height $n$ | $\delta$ | $\varphi(0)$ |
| (b) | $+n^2$ on $(-\tfrac1n,0)$, $-n^2$ on $(0,\tfrac1n)$ | $\delta'$ | $-\varphi'(0)$ |
| (c) | $\psi(x/n)$, $\psi\in C^\infty$ | $\psi(0)\,\mathbf 1$ | $\psi(0)\int\varphi$ |

All three sequences converge in $\mathcal D'(\mathbb R)$. The unifying mechanism is moment analysis under concentration/dilation. In (a) the mass is normalized to $1$ and nonnegative, so it samples $\varphi$ at the concentration point — a nascent $\delta$. In (b) the **antisymmetric** arrangement annihilates the zeroth moment ($\int g_n\to0$), and the surviving first moment $\int x\,g_n(x)\,dx\to-1$ produces $\delta'$ — the discrete analogue of "a $+/-$ pair of nearby point masses is a dipole." In (c), the dilation $x\mapsto x/n$ stretches $\psi$ until, against any fixed compactly supported test function, only the value $\psi(0)$ is seen — the weak-$*$ limit of a spreading profile is its central value times Lebesgue measure. The examples are the three canonical ways a sequence of $L^1_{\mathrm{loc}}$ functions can behave distributionally: concentrate to a point evaluation, concentrate antisymmetrically to a derivative, or spread to a constant.

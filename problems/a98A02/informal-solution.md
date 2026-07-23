<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98A02: A uniformly bounded orthonormal sequence is Riemann–Lebesgue against all of L¹

## Why It's Hard

We are handed two hypotheses on the sequence $(g_n)$ that live in *different* function spaces:

- **Orthonormality** $\int_0^1 g_n g_m = \delta_{nm}$ is an $L^2$ statement. It is exactly the input to **Bessel's inequality**, which immediately controls the pairings $\int f g_n$ when $f \in L^2$.
- **Uniform boundedness** $|g_n(x)| \le M$ is an $L^\infty$ statement. By itself it says nothing about decay of $\int f g_n$.

The target, however, is an $L^1$ statement: $\int_0^1 f g_n \to 0$ for *every* $f \in L^1$. The difficulty is that $L^1$ is the *largest* of these spaces — orthonormality gives us no Bessel-type series for an $L^1$ function (the relevant sum $\sum |\int f g_n|^2$ need not even converge), so we cannot argue directly. We must bootstrap from the dense subspace $L^2$ to all of $L^1$, and the *only* tool that bridges the gap is the uniform bound $M$. The hint ("start with $f$ in $L^2$") is telling us precisely this two-stage structure.

A second subtlety: the conclusion is **false** without the uniform bound. One can build orthonormal sequences (unbounded) for which $\int f g_n \not\to 0$ for some $f \in L^1$. So the proof must genuinely *use* $M$, not merely carry it along.

## The Key Insight

Think of each $g_n$ as defining a linear functional $f \mapsto \int_0^1 f g_n$ on $L^1$, with **operator norm exactly $\|g_n\|_\infty \le M$** — uniformly bounded in $n$. A family of uniformly bounded functionals that converges to $0$ on a *dense* subset converges to $0$ everywhere. Here:

1. **Dense subset $= L^2$.** Bessel's inequality forces $\int f g_n \to 0$ for $f \in L^2$, because $\sum_n |\int f g_n|^2 \le \|f\|_2^2 < \infty$ makes the terms a summable (hence null) sequence.
2. **Uniform bound $= M$.** For general $f \in L^1$, approximate by $h \in L^2$ in $L^1$-norm (possible since the measure is finite). The error $\int (f-h)g_n$ is controlled *uniformly in $n$* by $M\|f-h\|_1$ — this is the one and only place $M$ enters.

The $\varepsilon$ from approximation gets multiplied by $M$ (a constant), while the $L^2$ tail goes to $0$ in $n$. That is the whole argument.

## Complete Proof

Throughout, integrals are over $[0,1]$ with Lebesgue measure, which has total mass $1$. The hypotheses are: $(g_n)$ are measurable on $[0,1]$, $|g_n(x)| \le M$ for all $x$ and all $n$, and $\int g_n g_m = \delta_{nm}$ — i.e. $(g_n)$ is an **orthonormal** sequence in $L^2[0,1]$.

### Step 1 — The case $f \in L^2$ (Bessel's inequality)

Let $f \in L^2[0,1]$ and write $c_n := \int_0^1 f g_n = \langle f, g_n\rangle$. For any $N$, expand the nonnegative quantity $\big\| f - \sum_{n=1}^N c_n g_n\big\|_2^2$ using orthonormality:
$$
0 \le \Big\| f - \sum_{n=1}^N c_n g_n \Big\|_2^2
= \|f\|_2^2 - 2\sum_{n=1}^N c_n \langle f, g_n\rangle + \sum_{n=1}^N c_n^2
= \|f\|_2^2 - \sum_{n=1}^N c_n^2 .
$$
Hence $\sum_{n=1}^N c_n^2 \le \|f\|_2^2$ for every $N$, giving **Bessel's inequality**
$$
\sum_{n=1}^\infty \Big(\int_0^1 f g_n\Big)^2 = \sum_{n=1}^\infty c_n^2 \le \|f\|_2^2 < \infty .
$$
A convergent series has terms tending to $0$, so $c_n \to 0$, i.e.
$$
\int_0^1 f g_n \,dx \longrightarrow 0 \qquad (f \in L^2). \tag{1}
$$

### Step 2 — A uniform bound on the functionals

For *any* $\varphi \in L^1[0,1]$ and any $n$, the uniform bound $|g_n| \le M$ gives
$$
\left| \int_0^1 \varphi\, g_n \,dx \right| \le \int_0^1 |\varphi|\,|g_n|\,dx \le M \int_0^1 |\varphi|\,dx = M\,\|\varphi\|_1 . \tag{2}
$$
This holds with the *same* constant $M$ for all $n$ — the crucial uniformity.

### Step 3 — The case $f \in L^1$ (density + uniformity)

Let $f \in L^1[0,1]$ and fix $\varepsilon > 0$.

Since $[0,1]$ has finite measure, $L^2[0,1] \subseteq L^1[0,1]$ and $L^2$ is **dense** in $L^1$ (e.g. simple functions, or bounded truncations $f\cdot \mathbf 1_{|f|\le k}$, lie in $L^2$ and approximate $f$ in $L^1$ by dominated convergence). Choose $h \in L^2[0,1]$ with
$$
\|f - h\|_1 < \varepsilon .
$$
Split and apply $(2)$ to the difference $f-h \in L^1$ and $(1)$ to $h \in L^2$:
$$
\left| \int_0^1 f g_n \right|
\le \left| \int_0^1 (f-h) g_n \right| + \left| \int_0^1 h\, g_n \right|
\le M\,\|f-h\|_1 + \left| \int_0^1 h\, g_n \right|
< M\varepsilon + \left| \int_0^1 h\, g_n \right| .
$$
By Step 1, $\int_0^1 h g_n \to 0$, so there is $N$ with $\big|\int_0^1 h g_n\big| < \varepsilon$ for all $n \ge N$. For such $n$,
$$
\left| \int_0^1 f g_n \right| < M\varepsilon + \varepsilon = (M+1)\varepsilon .
$$
Therefore $\limsup_{n\to\infty}\big|\int_0^1 f g_n\big| \le (M+1)\varepsilon$. Since $\varepsilon > 0$ was arbitrary and $M$ is fixed,
$$
\boxed{\;\lim_{n\to\infty} \int_0^1 f(x)\, g_n(x)\,dx = 0 \quad\text{for every } f \in L^1[0,1].\;} \qquad \blacksquare
$$

### Remark — what each hypothesis buys, and a familiar instance

The two hypotheses play strictly complementary roles: **orthonormality** delivers decay on the dense subspace $L^2$ (Step 1), while the **uniform bound $M$** is what propagates that decay from the dense subspace to all of $L^1$ (Steps 2–3). Drop the bound and the conclusion can fail; drop orthonormality and there is no decay to propagate.

This is a clean abstraction of the **Riemann–Lebesgue lemma**: the trigonometric system $g_n(x) = \sqrt2\,\cos(2\pi n x)$ (or $\sqrt2\,\sin$) on $[0,1]$ is orthonormal and uniformly bounded by $M = \sqrt2$, and the result recovers $\int_0^1 f(x)\cos(2\pi n x)\,dx \to 0$ for all $f \in L^1$ — the statement that Fourier coefficients of integrable functions vanish at infinity.

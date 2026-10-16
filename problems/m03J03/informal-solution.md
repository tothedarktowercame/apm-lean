<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m03J03: Four distributions — Dirac comb, polynomial-growth Fourier series, derivatives of $H \cdot \sin$, and a non-example

## Why It's Hard

A "distribution" is not just *any* gadget that eats test functions and returns a
number. To be an element of $\mathcal{D}'(\mathbb{R})$ a functional $T$ must be **(i) linear** and
**(ii) continuous**, where continuity means a *seminorm estimate*: for every
compact $K$ there are $C, m$ with $|T(\varphi)| \leq C \sum_{j\leq m} \sup|\varphi^{(j)}|$ for all $\varphi$
supported in $K$. Each of the four parts probes a different way this can succeed
or fail, so the difficulty is that there is no single computation — you need the
right tool for each.

- **(a)** is an *infinite* sum that you must argue is locally finite, then bound.
- **(b)** is a series whose coefficients *grow* polynomially; it converges only
  because test functions are infinitely smooth, and the smoothness must be
  converted into decay by integration by parts. This is the polynomial-growth ↔
  rapid-decay duality that makes Fourier series of distributions work at all.
- **(c)** is a trap: you must track *which* boundary terms produce Dirac masses
  and which vanish. The function $H \cdot \sin$ is continuous at $0$ (so $D$ produces no
  delta), but its derivative $H \cdot \cos$ is *not* (so $D^{2}$ does).
- **(d)** looks like a distribution and is even continuous, but fails the most
  basic axiom — linearity — and the whole point is to notice that.

## The Key Insight

Every part reduces to controlling $T(\varphi)$ by finitely many derivative-seminorms of
$\varphi$ — and the absolute value $|\cdot|$ in part (d) is precisely what destroys the
*linear* structure those seminorms presuppose.

The load-bearing trick is **integration by parts against a test function**. In
(b) it turns $|a_n| \leq A|n|^N$ into a *summable* bound, because each integration
by parts pays a factor $1/|n|$ and $\varphi$ can be differentiated as many times as we
like: differentiate $N+2$ times and $\sum |n|^{-2} < \infty$ closes it. In (c) the *same*
integration by parts, but now watching the boundary term at $x=0$, is exactly the
bookkeeping that decides whether a $\delta$ appears: a boundary value of $\sin$ (which
is $0$) gives nothing, a boundary value of $\cos$ (which is $1$) gives $\delta$. The
clean check is that $H \cdot \sin$ is the causal fundamental solution of $D^{2}+1$:
$(D^{2}+1)(H\sin) = \delta$.

## Complete Proof

Throughout, $\mathcal{D}(\mathbb{R}) = C_c^\infty(\mathbb{R})$ is the space of smooth compactly supported test
functions, $\langle T,\varphi\rangle = T(\varphi)$, and $H$ is the Heaviside function ($H=1$ on $(0,\infty)$,
$H=0$ on $(-\infty,0)$). Distributional derivative is defined by
$\langle DT, \varphi\rangle = -\langle T, \varphi'\rangle$. A functional $T$ belongs to $\mathcal{D}'(\mathbb{R})$ iff it is linear and
satisfies, for each compact $K$, a bound
$|\langle T,\varphi\rangle| \leq C_K \sum_{j\leq m} \sup|\varphi^{(j)}|$ for all $\varphi$ with $\operatorname{supp} \varphi \subseteq K$.

---

### (a)  $T(\varphi) = \sum_{n=0}^\infty \varphi(n)$ is a distribution

**Well-defined and linear.** If $\operatorname{supp} \varphi \subseteq K$ with $K$ compact, then $\varphi(n) = 0$
for all but finitely many nonnegative integers $n$ (only those $n \in K$ survive).
So the sum is finite, and $T(\varphi) = \sum_{n\in K\cap \mathbb{Z}_{\geq 0}} \varphi(n)$. Linearity is immediate
from linearity of evaluation.

**Continuity (order 0).** Let $K$ be compact and let $p = \#(K \cap \mathbb{Z}_{\geq 0}) < \infty$ be
the number of nonnegative integers in $K$. For $\operatorname{supp} \varphi \subseteq K$,

$$|T(φ)| = \Big|\sum_{n \in K\cap\mathbb{Z}_{\ge 0}} φ(n)\Big| \le p\,\sup_x |φ(x)|.$$

This is the seminorm bound with $m = 0$, $C_K = p$. Hence $T \in \mathcal{D}'(\mathbb{R})$; in fact
$T = \sum_{n=0}^\infty \delta_n$, a locally finite sum of Dirac masses (a one-sided Dirac
comb), and it has order $0$. ∎

---

### (b)  $T = \sum_{n=0}^\infty a_n e^{inx}$ converges in $\mathcal{D}'(\mathbb{R})$ when $|a_n| \leq A|n|^N$

Each $e^{inx}$ is a smooth, bounded function, hence a distribution via
$\langle e^{inx}, \varphi\rangle = \int e^{inx} \varphi(x)\,dx$. Let $S_M = \sum_{n=0}^M a_n e^{inx}$ be the
partial sums. We show $\langle S_M, \varphi\rangle$ converges for every $\varphi \in \mathcal{D}$, with a limit that
is a distribution; that is exactly convergence in $\mathcal{D}'(\mathbb{R})$.

**Integration-by-parts decay.** Fix $\varphi \in \mathcal{D}$ and $n \geq 1$. Since
$e^{inx} = \frac{1}{in}\frac{d}{dx} e^{inx}$ and $\varphi$ has compact support, repeated
integration by parts (the boundary terms vanish) gives, for any $k \geq 0$,

$$\int e^{inx} φ(x)\,dx = \frac{(-1)^k}{(in)^k}\int e^{inx} φ^{(k)}(x)\,dx,
\qquad\text{so}\qquad
\Big|\int e^{inx} φ\,dx\Big| \le \frac{1}{|n|^{k}}\,\|φ^{(k)}\|_{L^1}.$$

**Absolute convergence.** Take $k = N+2$. Then for $n \geq 1$,

$$|a_n|\,\Big|\int e^{inx} φ\,dx\Big|
\le A|n|^{N}\cdot \frac{\|φ^{(N+2)}\|_{L^1}}{|n|^{N+2}}
= A\,\|φ^{(N+2)}\|_{L^1}\,\frac{1}{n^{2}},$$

and $\sum_{n\geq 1} n^{-2} < \infty$. The $n=0$ term is $a_0 \int \varphi$, finite. Hence
$\langle S_M, \varphi\rangle \to \langle T, \varphi\rangle := \sum_{n=0}^\infty a_n \int e^{inx}\varphi\,dx$ absolutely, for every $\varphi$.

**The limit is a distribution.** Summing the bound above, for $\operatorname{supp} \varphi \subseteq K$
(say $K \subseteq [-R,R]$, so $\Vert \psi\Vert_{L^1} \leq 2R\,\Vert \psi\Vert_\infty$),

$$|⟨T,φ⟩| \le |a_0|\,\|φ\|_{L^1} + A\Big(\sum_{n\ge1}\tfrac1{n^2}\Big)\|φ^{(N+2)}\|_{L^1}
\le C_K\Big(\sup|φ| + \sup|φ^{(N+2)}|\Big).$$

This is the seminorm estimate with $m = N+2$. So $T \in \mathcal{D}'(\mathbb{R})$, of order $\leq N+2$,
and the series converges to it in $\mathcal{D}'$. ∎

---

### (c)  $D(H\sin)$ and $D^2(H\sin)$

Write $g(x) = H(x)\sin x$ (equal to $\sin x$ for $x>0$, and $0$ for $x<0$). Note
$g$ is **continuous** at $0$ because $\sin 0 = 0$.

**Claim.** $D(H\sin) = H(x)\cos x$ and $D^2(H\sin) = \delta - H(x)\sin x$.

**Heuristic (Leibniz with $H' = \delta$).**
$D(H\sin) = H'\sin + H\cos = (\sin 0)\,\delta + H\cos = H\cos$, since the delta is
weighted by $\sin 0 = 0$. Then
$D^2(H\sin) = D(H\cos) = H'\cos + H(\cos)' = (\cos 0)\,\delta - H\sin = \delta - H\sin$,
since now the delta is weighted by $\cos 0 = 1$.

**Verification from the definition.** For the first derivative and any $\varphi \in \mathcal{D}$,

$$⟨D(H\sin), φ⟩ = -⟨H\sin, φ'⟩ = -\int_0^\infty \sin x\,φ'(x)\,dx
= -\Big([\sin x\,φ(x)]_0^\infty - \int_0^\infty \cos x\,φ(x)\,dx\Big).$$

The boundary term vanishes ($\varphi(\infty)=0$ by compact support, and $\sin 0 = 0$), so
this equals $\int_0^\infty \cos x\,\varphi\,dx = \langle H\cos, \varphi\rangle$. Thus $D(H\sin) = H\cos$. ✓

For the second derivative,

$$⟨D^2(H\sin), φ⟩ = ⟨H\sin, φ''⟩ = \int_0^\infty \sin x\,φ''(x)\,dx.$$

Integrate by parts once: $= [\sin x\,\varphi']_0^\infty - \int_0^\infty \cos x\,\varphi'\,dx
= -\int_0^\infty \cos x\,\varphi'\,dx$ (boundary term $0$, as $\sin 0 = 0$). Integrate again:

$$-\int_0^\infty \cos x\,φ'\,dx
= -\Big([\cos x\,φ]_0^\infty - \int_0^\infty(-\sin x)φ\,dx\Big)
= -\big(-φ(0)\big) - \int_0^\infty \sin x\,φ\,dx = φ(0) - ⟨H\sin, φ⟩.$$

Here the boundary term contributes $-\cos 0\,\varphi(0) = -\varphi(0)$ at the lower limit.
Hence $\langle D^2(H\sin),\varphi\rangle = \langle \delta,\varphi\rangle - \langle H\sin,\varphi\rangle$, i.e. $D^2(H\sin) = \delta - H\sin$. ✓

**Consistency check.** Combining, $(D^2 + 1)(H\sin) = \delta$: $H(x)\sin x$ is the
causal fundamental solution of the operator $D^2 + 1$, as expected. ∎

---

### (d)  $T(\varphi) = |\varphi(0)|$ is **not** a distribution

A distribution must be **linear**. The functional $T(\varphi) = |\varphi(0)|$ is not, and a
single explicit pair of test functions exhibits the failure.

- *Homogeneity fails for negative scalars.* For any $\varphi$ with $\varphi(0) \neq 0$,
  $T(-\varphi) = |-\varphi(0)| = |\varphi(0)| = T(\varphi) \neq -T(\varphi)$.
- *Additivity fails.* Choose $\varphi, \psi \in \mathcal{D}$ with $\varphi(0) = 1$ and $\psi(0) = -1$ (e.g. a
  bump $\chi$ with $\chi(0)=1$, and $\varphi = \chi$, $\psi = -\chi$). Then

$$T(φ + ψ) = |φ(0) + ψ(0)| = |0| = 0,
\quad\text{but}\quad T(φ) + T(ψ) = 1 + 1 = 2.$$

Since $T(\varphi+\psi) \neq T(\varphi) + T(\psi)$, $T$ is not linear. (It is continuous and even
positively homogeneous — but linearity is part of the *definition* of $\mathcal{D}'(\mathbb{R})$,
and it is exactly the property the absolute value destroys.) Therefore $T$ does
not define an element of $\mathcal{D}'(\mathbb{R})$. ∎

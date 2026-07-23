<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM aunk05: The Weierstrass convergence theorem — holomorphy and derivatives survive locally uniform limits

## Why It's Hard

The statement is *false in real analysis*, and that is precisely what makes it subtle. A uniformly convergent sequence of smooth real functions need not have a differentiable limit (e.g. $\sqrt{x^2+1/n}\to|x|$), and even when the limit is differentiable the derivatives need not converge (e.g. $\frac{\sin(nx)}{n}\to0$ uniformly while the derivatives $\cos(nx)$ converge to nothing). So **no real-variable estimate can possibly work** — the result is a genuine rigidity phenomenon special to holomorphic functions, and the proof must draw on complex-analytic machinery (Cauchy theory), not $\varepsilon$–$\delta$ differentiation.

This forces an indirect route in both parts:

- **Part (a)** cannot establish holomorphy by differentiating $f$ (we have no control on difference quotients). Instead one must characterize holomorphy *integrally* — via **Morera's theorem** — and exploit the fact that uniform convergence interacts beautifully with **integration** (limit and contour integral commute on a compact contour), even though it interacts badly with differentiation.

- **Part (b)** is the surprising upgrade: uniform convergence of the *functions* forces uniform convergence of *all derivatives*. The only tool strong enough is the **Cauchy integral formula for derivatives**, which re-expresses differentiation as integration against a kernel. The technical crux is keeping a fixed buffer distance $r$ from the boundary, which is what supplies the constant in the estimate.

## The Key Insight

In complex analysis, **differentiation is secretly integration**:
$$
f'(z)=\frac{1}{2\pi i}\oint_{|\zeta-z|=r}\frac{f(\zeta)}{(\zeta-z)^2}\,d\zeta,
$$
and uniform convergence **commutes with contour integration** over a compact curve (the error is bounded by length × sup-norm). So *both* parts reduce to the single move "pass the uniform limit through a contour integral":

- For (a), the integral of $f_n$ around every triangle is $0$ (Cauchy–Goursat); passing the limit, the same holds for $f$, and **Morera** upgrades this to holomorphy.
- For (b), apply the Cauchy derivative formula to the holomorphic difference $f_n-f$ on circles of radius $r$ sitting inside $\Omega$: the kernel $(\zeta-z)^{-2}$ turns $\sup|f_n-f|$ into a bound on $\sup|f_n'-f'|$, losing only a harmless factor $1/r$.

## Complete Proof

Throughout, "uniformly on compact subsets" (locally uniformly) means: for every compact $K\subset\Omega$, $\sup_{K}|f_n-f|\to0$.

### Part (a): $f$ is holomorphic in $\Omega$

**$f$ is continuous.** Each point of $\Omega$ has a compact neighborhood (a closed disk $\subset\Omega$); on it $f_n\to f$ uniformly, and a uniform limit of continuous functions is continuous. Continuity is local, so $f$ is continuous on $\Omega$.

**$f$ satisfies Morera's hypothesis.** Let $D\subset\Omega$ be any open disk and let $\Delta\subset D$ be any (solid) triangle; its boundary $\partial\Delta$ is a compact subset of $\Omega$ with finite length $L$. Each $f_n$ is holomorphic, so by the **Cauchy–Goursat theorem** $\oint_{\partial\Delta}f_n\,dz=0$. Since $f_n\to f$ uniformly on the compact set $\partial\Delta$,
$$
\left|\oint_{\partial\Delta}f\,dz-\oint_{\partial\Delta}f_n\,dz\right|=\left|\oint_{\partial\Delta}(f-f_n)\,dz\right|\le L\cdot\sup_{\partial\Delta}|f-f_n|\xrightarrow[n\to\infty]{}0,
$$
so $\oint_{\partial\Delta}f\,dz=\lim_{n}\oint_{\partial\Delta}f_n\,dz=0$.

**Morera's theorem** (*if $g$ is continuous on a disk $D$ and $\oint_{\partial\Delta}g\,dz=0$ for every triangle $\Delta\subset D$, then $g$ is holomorphic on $D$*) now gives that $f$ is holomorphic on $D$. As $\Omega$ is covered by such disks and holomorphy is a local property, $f$ is holomorphic on all of $\Omega$. $\qquad\checkmark$

### Part (b): $f_n'\to f'$ uniformly on compact subsets

Fix a compact set $K\subset\Omega$. Since $K$ is compact and $\Omega^c$ is closed and disjoint from $K$, the distance $d:=\operatorname{dist}(K,\Omega^c)>0$ (interpret $d=+\infty$ if $\Omega=\mathbb{C}$). Fix any radius $r$ with $0<r<d$, and set
$$
K_r:=\{\,w\in\mathbb{C}:\operatorname{dist}(w,K)\le r\,\}.
$$
Then $K_r$ is compact and $K_r\subset\Omega$ (every point of $K_r$ is within $r<d$ of $K$). For each $z\in K$, the circle $\gamma_z=\{\zeta:|\zeta-z|=r\}$ and its interior lie in $K_r\subset\Omega$.

By part (a), $f$ is holomorphic, so $g_n:=f_n-f$ is holomorphic on $\Omega$. The **Cauchy integral formula for the first derivative** applied to $g_n$ on $\gamma_z$ gives
$$
g_n'(z)=f_n'(z)-f'(z)=\frac{1}{2\pi i}\oint_{\gamma_z}\frac{g_n(\zeta)}{(\zeta-z)^2}\,d\zeta .
$$
Estimate, using $|\zeta-z|=r$ on $\gamma_z$ and length $2\pi r$:
$$
|f_n'(z)-f'(z)|\le\frac{1}{2\pi}\cdot(2\pi r)\cdot\frac{\sup_{\zeta\in\gamma_z}|g_n(\zeta)|}{r^2}
=\frac{1}{r}\,\sup_{\zeta\in\gamma_z}|f_n(\zeta)-f(\zeta)|\le\frac{1}{r}\,\sup_{K_r}|f_n-f|,
$$
where the last step uses $\gamma_z\subset K_r$. The bound on the right is **independent of $z\in K$**, so
$$
\sup_{z\in K}|f_n'(z)-f'(z)|\le\frac{1}{r}\,\sup_{K_r}|f_n-f|\xrightarrow[n\to\infty]{}0,
$$
because $f_n\to f$ uniformly on the compact set $K_r$. Hence $f_n'\to f'$ uniformly on $K$, and since $K$ was an arbitrary compact subset, $f_n'\to f'$ uniformly on compact subsets of $\Omega$. $\qquad\blacksquare$

### Remark — the cascade and a sharper statement

Part (b) self-improves: applying it to the sequence $(f_n')\to f'$ (now itself a locally-uniformly convergent sequence of holomorphic functions, by (a) and (b)) shows $f_n''\to f''$ locally uniformly, and by induction $f_n^{(k)}\to f^{(k)}$ locally uniformly for **every** $k\ge0$. The quantitative heart is the Cauchy derivative estimate $\big|(f_n-f)^{(k)}(z)\big|\le\frac{k!}{r^k}\sup_{K_r}|f_n-f|$, which converts a single sup-bound on the functions into simultaneous control of all derivatives. This is exactly the rigidity that fails in the real category: holomorphic functions are determined by, and vary continuously with, their values on circles — and "values on circles" is what uniform convergence controls. (The result is the analytic engine behind, e.g., the holomorphy of power series, Dirichlet series such as $\zeta$, and limits like the ones appearing in aunk03/a98A07 in this set.)

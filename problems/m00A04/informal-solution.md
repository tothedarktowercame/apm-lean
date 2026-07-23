<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m00A04: Minimizing ½‖v‖²−f(v) proves Riesz representation and solves −Δu+u=F weakly

## Why It's Hard

This is the **direct method of the calculus of variations** in its purest form, used to
prove the Riesz representation theorem and then to solve an elliptic boundary value
problem with no extra machinery. The subtlety in (a) is that "bounded below" is easy
(coercivity), but producing the *minimizer* needs more than a minimizing sequence — you
must show it converges, which works because $\varphi$ is **uniformly convex** (a
parallelogram-identity computation) and $V$ is **complete**. Part (b) is the
Euler–Lagrange/first-variation step, and (c) is the leap to PDE: choosing the Sobolev
space $H^1_0(\Omega)$ with the *energy inner product* turns the abstract theorem into
existence and uniqueness of a weak solution, with the boundary condition hidden inside the
choice of space.

## The Key Insight

- **(a)** $\varphi(v)\ge\tfrac12\|v\|^2-\|f\|\,\|v\|\ge-\tfrac12\|f\|^2$ (coercive,
  bounded below); and the parallelogram identity gives
  $\tfrac14\|u-v\|^2=\varphi(u)+\varphi(v)-2\varphi(\tfrac{u+v}{2})$, so a minimizing
  sequence is Cauchy — completeness yields a unique minimizer.
- **(b)** $\varphi(u+tv)-\varphi(u)=t\,[(u,v)-f(v)]+\tfrac{t^2}{2}\|v\|^2\ge0$ for all
  $t$ forces $(u,v)=f(v)$.
- **(c)** With $V=H^1_0(\Omega)$, $(u,v)_V=\int_\Omega(\nabla u\!\cdot\!\nabla v+uv)$, and
  $f(v)=\int_\Omega Fv$, the minimizer $u$ satisfies $\int(\nabla u\!\cdot\!\nabla
  v+uv)=\int Fv$ for all $v$ — the weak form of $-\Delta u+u=F$, $u|_{\partial\Omega}=0$.

## Complete Proof

$V$ is a real Hilbert space, $f\in V'$, and $\varphi(v)=\tfrac12\|v\|^2-f(v)$.

### (a) $\varphi$ is bounded below with a unique minimizer

**Bounded below (coercive).** By continuity of $f$, $|f(v)|\le\|f\|\,\|v\|$, so
$$
\varphi(v)\ge\tfrac12\|v\|^2-\|f\|\,\|v\|=\tfrac12\big(\|v\|-\|f\|\big)^2-\tfrac12\|f\|^2
\ \ge\ -\tfrac12\|f\|^2 .
$$
Thus $m:=\inf_{v\in V}\varphi(v)\ge-\tfrac12\|f\|^2>-\infty$, and moreover
$\varphi(v)\to+\infty$ as $\|v\|\to\infty$.

**Uniform convexity (parallelogram identity).** For any $u,v\in V$, expand using
$\|u+v\|^2+\|u-v\|^2=2\|u\|^2+2\|v\|^2$ and linearity of $f$:
$$
\varphi(u)+\varphi(v)-2\,\varphi\!\Big(\tfrac{u+v}{2}\Big)
=\tfrac12\|u\|^2+\tfrac12\|v\|^2-\tfrac14\|u+v\|^2
=\tfrac14\|u-v\|^2. \tag{$\ast$}
$$
(The $f$-terms cancel because $f(u)+f(v)-2f(\tfrac{u+v}{2})=0$.)

**Existence.** Take a minimizing sequence $v_n$ with $\varphi(v_n)\to m$. By $(\ast)$,
since $\varphi(\tfrac{v_n+v_k}{2})\ge m$,
$$
\tfrac14\|v_n-v_k\|^2=\varphi(v_n)+\varphi(v_k)-2\varphi\!\Big(\tfrac{v_n+v_k}{2}\Big)
\le \varphi(v_n)+\varphi(v_k)-2m\xrightarrow[n,k\to\infty]{}0 .
$$
So $(v_n)$ is Cauchy; as $V$ is complete, $v_n\to u\in V$. Since $\varphi$ is continuous
($\|\cdot\|^2$ and $f$ are), $\varphi(u)=\lim\varphi(v_n)=m$, so $u$ is a minimizer.

**Uniqueness.** If $\varphi(u)=\varphi(u')=m$, then $(\ast)$ gives
$\tfrac14\|u-u'\|^2\le m+m-2m=0$, so $u=u'$. Hence the minimizer is unique, and
$v\neq u\Rightarrow\varphi(v)>\varphi(u)$. $\quad\checkmark$

### (b) The minimizer represents $f$: $(u,v)_V=f(v)$ for all $v$

Fix $v\in V$ and consider, for $t\in\mathbb{R}$,
$$
\varphi(u+tv)=\tfrac12\|u+tv\|^2-f(u+tv)
=\varphi(u)+t\big[(u,v)-f(v)\big]+\tfrac{t^2}{2}\|v\|^2 .
$$
Since $u$ minimizes $\varphi$, $\varphi(u+tv)-\varphi(u)\ge0$ for all $t$, i.e.
$$
t\big[(u,v)-f(v)\big]+\tfrac{t^2}{2}\|v\|^2\ \ge\ 0\qquad\forall t .
$$
Write $c=(u,v)-f(v)$. If $c\neq0$, choosing $t$ small with the sign opposite to $c$ makes
$ct+\tfrac{t^2}{2}\|v\|^2<0$ (the linear term dominates near $0$) — a contradiction.
Hence $c=0$, i.e.
$$
(u,v)_V=f(v)\qquad\text{for all }v\in V. \qquad\checkmark
$$
(Parts (a)–(b) are precisely the Riesz Representation Theorem, proved variationally:
$u$ is the unique vector representing $f$.)

### (c) Weak solvability of $-\Delta u+u=F$, $u|_{\partial\Omega}=0$

Let $\Omega\subset\mathbb{R}^n$ be a bounded domain and $F\in L^2(\Omega)$. Choose
$$
V=H^1_0(\Omega)=\overline{C_c^\infty(\Omega)}^{\;\|\cdot\|_{H^1}},\qquad
(u,v)_V=\int_\Omega\big(\nabla u\cdot\nabla v+uv\big)\,dx ,
$$
the closure of smooth compactly supported functions in the $H^1$-norm. This is a real
Hilbert space, and the displayed bilinear form is exactly the $H^1$ inner product, with
$\|v\|_V^2=\int_\Omega(|\nabla v|^2+v^2)=\|v\|_{H^1}^2$. (The "$+u$" term is what makes
this form coercive automatically — no Poincaré inequality is needed.) Define
$$
f(v)=\int_\Omega F\,v\,dx .
$$
Then $f$ is linear, and continuous on $V$: by Cauchy–Schwarz,
$|f(v)|\le\|F\|_{L^2}\|v\|_{L^2}\le\|F\|_{L^2}\|v\|_{H^1}=\|F\|_{L^2}\|v\|_V$, so $f\in
V'$.

By parts (a)–(b) applied to this $V$ and $f$, there is a unique $u\in H^1_0(\Omega)$
(the minimizer of $\varphi(v)=\tfrac12\int_\Omega(|\nabla v|^2+v^2)-\int_\Omega Fv$) with
$$
\boxed{\ \int_\Omega\big(\nabla u\cdot\nabla v+u\,v\big)\,dx=\int_\Omega F\,v\,dx
\qquad\text{for all }v\in H^1_0(\Omega).\ } \tag{W}
$$

**What "weak solution" means.** A weak solution of the boundary value problem
$$
-\Delta u+u=F\ \text{in }\Omega,\qquad u=0\ \text{on }\partial\Omega,
$$
is a function $u\in H^1_0(\Omega)$ satisfying $(\mathrm W)$ for every test function $v\in
H^1_0(\Omega)$ (equivalently, by density, for every $v\in C_c^\infty(\Omega)$). The
Dirichlet boundary condition $u=0$ on $\partial\Omega$ is encoded by membership in
$H^1_0(\Omega)$ (functions with zero trace). Formula $(\mathrm W)$ is the integration-by-
parts form of the PDE: for smooth $u$ and $v\in C_c^\infty(\Omega)$,
$\int_\Omega\nabla u\cdot\nabla v=-\int_\Omega(\Delta u)v$ (no boundary term, as $v$
vanishes near $\partial\Omega$), so $(\mathrm W)$ reads $\int_\Omega(-\Delta u+u-F)v=0$
for all such $v$, i.e. $-\Delta u+u=F$ in the distributional sense.

Thus the variational principle produces a unique weak solution $u\in H^1_0(\Omega)$.
$\quad\blacksquare$

### Remark

Parts (a)–(b) are the variational proof of Riesz representation; part (c) is the special
case that, when the abstract inner product is realized as the *energy form* of a coercive
elliptic operator, "the vector representing $f$" is exactly "the weak solution of the
PDE." The operator $-\Delta+I$ is the canonical example because its energy form *is* the
full $H^1$ inner product, so coercivity is free; for $-\Delta$ alone one restores
coercivity on $H^1_0$ via the Poincaré inequality. This is the heart of the Lax–Milgram /
finite-element framework: existence, uniqueness, and the variational ("minimum energy")
characterization all at once.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m03J01: Minimizing a quadratic functional — Riesz representation, the Dirichlet problem, and elliptic regularity by closed graph

## Why It's Hard

This five-part problem reconstructs the entire variational-PDE pipeline from
scratch, and each part needs a *different* tool:

- **(a)** Existence of a minimizer is **not** a soft compactness argument: a
  Hilbert ball is not norm-compact. The proof instead extracts a minimizing
  sequence and shows it is **Cauchy** via a clever application of the
  parallelogram law — the same identity that powers the Hilbert projection
  theorem. Recognizing that the parallelogram law is what makes the sequence
  Cauchy is the crux.
- **(b)** is the **first variation**: differentiating $t\mapsto\varphi(u+tv)$ at
  the minimum recovers exactly the **Riesz representation** identity. The
  problem is secretly a from-scratch proof of the Riesz representation theorem.
- **(c)** is an operator-norm estimate that hides the fact that $f\mapsto u$ is
  an **isometry** of $V'$ onto $V$.
- **(d)** demands choosing the *right* Hilbert space ($H_0^1$ with the energy
  inner product), recognizing that the Dirichlet boundary condition is encoded
  in the *space* (trace zero) rather than the equation, and deriving the weak
  form by integration by parts.
- **(e)** asks to upgrade a purely **qualitative** regularity implication
  ($F\in L^2 \Rightarrow u\in H^2$) to a **quantitative** bound
  $\|u\|_{H^2}\le C\|F\|_{L^2}$. The only tool that does this from the bare
  implication is the **closed graph theorem**.

## The Key Insight

Once a minimizer $u$ exists, **completing the square** reveals everything:
$$\varphi(v) = \tfrac12\|v\|^2 - f(v) = \tfrac12\|v-u\|^2 - \tfrac12\|u\|^2,$$
so minimizing $\varphi$ is the same as projecting onto the Riesz representative
$u$ of $f$, and the first-order condition $(u,v)=f(v)$ *is* the weak equation.
The parallelogram law is what forces minimizing sequences to be Cauchy; the
first variation is what turns the minimizer into a solution of the variational
equation. For the PDE, the single choice $V=H_0^1(\Omega)$ with
$(u,v)_V=\int_\Omega(\nabla u\cdot\nabla v + uv)$ converts $-\Delta u+u=F$ into
exactly the abstract identity $(u,v)_V=f(v)$.

## Complete Proof

Throughout, $V$ is a real Hilbert space, $f\in V'$ with operator norm
$\|f\|_{V'}=\sup_{\|v\|\le 1}|f(v)|$, and $\varphi(v)=\tfrac12\|v\|^2-f(v)$.

### Part (a) — $\varphi$ is bounded below and has a unique minimizer

**Bounded below.** Since $f$ is continuous, $|f(v)|\le\|f\|_{V'}\|v\|$, so with
$t=\|v\|\ge 0$,
$$\varphi(v)\ \ge\ \tfrac12\|v\|^2-\|f\|_{V'}\|v\| \ =\ \tfrac12 t^2-\|f\|_{V'}t.$$
The scalar quadratic $\tfrac12 t^2-\|f\|_{V'}t$ has minimum value
$-\tfrac12\|f\|_{V'}^2$ (at $t=\|f\|_{V'}$). Hence
$$\varphi(v)\ \ge\ -\tfrac12\|f\|_{V'}^2 \qquad\text{for all }v\in V,$$
so $\varphi$ is bounded below. Set $m:=\inf_{v\in V}\varphi(v)>-\infty$.

**Existence via a Cauchy minimizing sequence.** Choose $(v_n)\subset V$ with
$\varphi(v_n)\to m$. The key identity: for any $a,b\in V$, expanding norms and
using linearity of $f$,
$$\|a-b\|^2 \;=\; 4\varphi(a)+4\varphi(b)-8\,\varphi\!\Big(\tfrac{a+b}{2}\Big). \tag{$\star$}$$
*(Check: $4\varphi(a)+4\varphi(b)=2\|a\|^2+2\|b\|^2-4f(a)-4f(b)$, while
$8\varphi(\tfrac{a+b}{2})=\|a+b\|^2-4f(a)-4f(b)$; subtracting gives
$2\|a\|^2+2\|b\|^2-\|a+b\|^2=\|a-b\|^2$, the parallelogram law. The
$f$-terms cancel exactly.)*

Apply $(\star)$ with $a=v_n,\ b=v_m$. Since
$\varphi\big(\tfrac{v_n+v_m}{2}\big)\ge m$,
$$\|v_n-v_m\|^2 \;\le\; 4\varphi(v_n)+4\varphi(v_m)-8m \;\xrightarrow[n,m\to\infty]{}\; 4m+4m-8m=0.$$
Thus $(v_n)$ is Cauchy; by completeness of $V$, $v_n\to u$ for some $u\in V$.
Since the norm and $f$ are continuous, $\varphi$ is continuous, so
$\varphi(u)=\lim_n\varphi(v_n)=m$. Hence $u$ realizes the minimum.

**Uniqueness.** If $u'$ also satisfies $\varphi(u')=m$, apply $(\star)$ with
$a=u,\ b=u'$:
$$\|u-u'\|^2 \le 4\varphi(u)+4\varphi(u')-8\,\varphi\!\Big(\tfrac{u+u'}{2}\Big)
\le 4m+4m-8m = 0,$$
so $u=u'$. The minimizer is unique. $\blacksquare$

### Part (b) — The minimizer satisfies $(u,v)_V=f(v)$ for all $v$

Fix $v\in V$ and consider $g(t):=\varphi(u+tv)$ for $t\in\mathbb R$. Expanding,
$$g(t)=\tfrac12\|u\|^2+t\,(u,v)+\tfrac{t^2}{2}\|v\|^2-f(u)-t\,f(v),$$
a smooth quadratic in $t$ with $g'(t)=(u,v)+t\|v\|^2-f(v)$. Because $u$
minimizes $\varphi$, the function $g$ has a global minimum at $t=0$, so
$g'(0)=0$:
$$(u,v)-f(v)=0,\qquad\text{i.e.}\qquad \boxed{(u,v)_V=f(v)\quad\forall v\in V.}$$
(This exhibits $u$ as the **Riesz representative** of $f$.) $\blacksquare$

### Part (c) — $f\mapsto u$ is continuous from $V'$ to $V$

**Linearity.** Let $u_1,u_2$ represent $f_1,f_2$ as in (b). For all $v$,
$$(\alpha u_1+\beta u_2,\,v)=\alpha f_1(v)+\beta f_2(v)=(\alpha f_1+\beta f_2)(v),$$
so by the uniqueness in (a)–(b), $\alpha u_1+\beta u_2$ is the representative of
$\alpha f_1+\beta f_2$. Hence the map $T:f\mapsto u$ is linear.

**Boundedness.** Taking $v=u$ in (b),
$$\|u\|^2=(u,u)=f(u)\le\|f\|_{V'}\|u\|\ \Longrightarrow\ \|u\|\le\|f\|_{V'}.$$
(Conversely $|f(v)|=|(u,v)|\le\|u\|\|v\|$ gives $\|f\|_{V'}\le\|u\|$, so in fact
$\|u\|=\|f\|_{V'}$: $T$ is an isometry.) By linearity,
$$\|T f_1-T f_2\|=\|T(f_1-f_2)\|\le\|f_1-f_2\|_{V'},$$
so $T$ is $1$-Lipschitz, hence continuous. $\blacksquare$

### Part (d) — Unique weak solution of $-\Delta u+u=F$, $\ u=0$ on $\partial\Omega$

Let $\Omega\subset\mathbb R^n$ be a bounded domain.

**Choice of space.** Take
$$V=H_0^1(\Omega),\qquad (u,v)_V:=\int_\Omega\big(\nabla u\cdot\nabla v+uv\big)\,dx,
\qquad \|v\|_V^2=\int_\Omega\big(|\nabla v|^2+v^2\big)\,dx.$$
This is the full $H^1$ inner product; $H_0^1(\Omega)$ (the closure of
$C_c^\infty(\Omega)$ in the $H^1$ norm) is a closed subspace of $H^1$, hence a
Hilbert space. The homogeneous Dirichlet condition $u=0$ on $\partial\Omega$ is
encoded by membership in $H_0^1$ (zero trace).

**Assumption on $F$ and the functional.** Assume $F\in L^2(\Omega)$ and define
$$f(v):=\int_\Omega F\,v\,dx.$$
By Cauchy–Schwarz, $|f(v)|\le\|F\|_{L^2}\|v\|_{L^2}\le\|F\|_{L^2}\|v\|_V$, so
$f\in V'$ with $\|f\|_{V'}\le\|F\|_{L^2}$.

**Weak formulation.** A function $u\in H_0^1(\Omega)$ is a **weak solution** if
$$\int_\Omega\big(\nabla u\cdot\nabla v+uv\big)\,dx=\int_\Omega F\,v\,dx
\qquad\forall v\in H_0^1(\Omega). \tag{W}$$
*Motivation.* If $u$ is smooth and solves $-\Delta u+u=F$ classically, multiply
by $v\in C_c^\infty(\Omega)$ and integrate; Green's identity gives
$\int_\Omega(-\Delta u)v=\int_\Omega\nabla u\cdot\nabla v$ (no boundary term,
since $v$ vanishes near $\partial\Omega$), so
$\int_\Omega(\nabla u\cdot\nabla v+uv)=\int_\Omega Fv$. By density of
$C_c^\infty$ in $H_0^1$, this extends to all test functions $v\in H_0^1$, which
is (W). Conversely, (W) requires only one weak derivative of $u$, so it makes
sense for $u\in H_0^1$ and is the natural relaxed notion.

**Existence and uniqueness.** With this $V$ and $f$, (W) is *verbatim* the
identity $(u,v)_V=f(v)$ of part (b). By parts (a)–(b) the functional
$\varphi(v)=\tfrac12\|v\|_V^2-f(v)$ has a unique minimizer $u\in H_0^1$, and that
minimizer is the unique element satisfying (W). Hence the boundary-value problem
has a **unique weak solution**. $\blacksquare$

### Part (e) — $F\mapsto u$ is continuous from $L^2(\Omega)$ to $H^2(\Omega)$

Let $S:F\mapsto u$ be the solution map of (d). We are given the regularity
**implication**: $F\in L^2(\Omega)\Rightarrow u\in H^2(\Omega)$, so $S$ maps
$L^2(\Omega)$ into $H^2(\Omega)$. We show $S$ is bounded.

**$S$ is linear.** It is the composition $F\mapsto f=\langle F,\cdot\rangle_{L^2}$
(linear) followed by $f\mapsto u$ (linear, by (c)).

**$S$ is continuous via the closed graph theorem.** $L^2(\Omega)$ and
$H^2(\Omega)$ are Banach spaces and $S:L^2\to H^2$ is linear; it suffices to show
its graph is closed. Suppose
$$F_k\to F\ \text{ in } L^2(\Omega),\qquad u_k:=S F_k\to w\ \text{ in } H^2(\Omega).$$
We must show $w=SF$.

- From (c)–(d), the map $L^2\to V=H_0^1$, $F\mapsto u$, is continuous because
  $\|u\|_V\le\|f\|_{V'}\le\|F\|_{L^2}$. Hence $F_k\to F$ in $L^2$ forces
  $u_k\to SF$ in $H_0^1$.
- The inclusion $H^2(\Omega)\hookrightarrow H^1(\Omega)$ is continuous, so
  $u_k\to w$ in $H^2$ implies $u_k\to w$ in $H^1$, a fortiori in $H_0^1$.

By uniqueness of limits in $H^1$, $w=SF$. Thus the graph of $S$ is closed, and
by the closed graph theorem $S$ is bounded:
$$\|SF\|_{H^2(\Omega)}\le C\,\|F\|_{L^2(\Omega)}\qquad\text{for some }C<\infty,$$
i.e. $F\mapsto u$ is continuous from $L^2(\Omega)$ to $H^2(\Omega)$.
$\blacksquare$

*Constructive alternative.* When the regularity hypothesis is available in its
quantitative form $\|u\|_{H^2}\le C(\|\Delta u\|_{L^2}+\|u\|_{L^2})$, one argues
directly: from the equation $-\Delta u=F-u$ and the energy bound
$\|u\|_{L^2}\le\|u\|_V\le\|F\|_{L^2}$,
$$\|u\|_{H^2}\le C\big(\|F-u\|_{L^2}+\|u\|_{L^2}\big)\le C\big(\|F\|_{L^2}+2\|u\|_{L^2}\big)\le 3C\,\|F\|_{L^2}.$$
The closed-graph route is preferred here because the problem supplies only the
*qualitative* implication.

## What Connects

**To the Riesz representation theorem.** Parts (a)–(c) are a complete,
self-contained proof of Riesz representation by minimization: every $f\in V'$ has
a unique representative $u$ with $f(v)=(u,v)$, and $f\mapsto u$ is an isometric
isomorphism $V'\cong V$. The parallelogram law is doing the same work it does in
the Hilbert projection theorem.

**To Lax–Milgram.** This is the symmetric case of Lax–Milgram: the bilinear
form $a(u,v)=(u,v)_V$ is symmetric, bounded, and coercive, so the variational
problem is equivalent to minimizing the energy $\varphi$. The nonsymmetric
Lax–Milgram theorem drops the energy-minimization picture but keeps the
existence/uniqueness conclusion.

**To the finite element method.** The weak form (W) is exactly what is
discretized in Galerkin/finite-element schemes: replace $H_0^1$ by a
finite-dimensional subspace $V_h$ and solve $(u_h,v)_V=f(v)$ for all $v\in V_h$.
Céa's lemma then bounds the error by the best approximation error, using the same
coercivity that gives uniqueness here.

**To elliptic regularity theory.** Part (e) is the abstract shadow of elliptic
regularity: the solution operator $(-\Delta+I)^{-1}$ gains two derivatives,
mapping $L^2\to H^2$ boundedly. The closed graph theorem is the standard device
for converting a regularity *existence* statement into the operator-norm
*estimate* needed downstream (e.g. for spectral theory of the Dirichlet
Laplacian, where compactness of $H^2\hookrightarrow L^2$ yields a discrete
spectrum).

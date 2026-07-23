<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m03J04: Adjoints, annihilators, and the inf-sup condition — the closed-range theorem behind Babuška–Brezzi

## Why It's Hard

This four-part problem assembles the abstract machinery underlying the
**Babuška–Brezzi (inf-sup) theory** of saddle-point problems, and each part
hinges on a different functional-analytic tool:

- **(a)** The adjoint is defined through the *bilinear pairing*
  $b(v,w)=(Bv)(w)$. Showing $(B')'=B$ looks like a triviality but quietly uses
  **reflexivity** ($W''=W$, $V''=V$, true because they are Hilbert spaces) to
  make the double adjoint land back in the right space.
- **(b)** is routine, but the clean proof recognizes the annihilator as an
  **intersection of kernels of evaluation functionals**, which makes closedness
  immediate.
- **(c)** is one half of the **closed range theorem**:
  $\overline{B(V)}=(\ker B')^o$. The hard inclusion needs **Hahn–Banach
  separation**, and then reflexivity of $W$ to realize the separating functional
  as *evaluation at a point* $w_0\in W$ — that is exactly what converts "$\Phi$
  kills $B(V)$" into "$w_0\in\ker B'$".
- **(d)** The **inf-sup condition** $\|Bv\|_{W'}\ge\alpha\|v\|_V$ must be
  decoded: the deceptively-written $\sup_w B_v(w)/\|w\|$ *is* the dual norm
  $\|Bv\|_{W'}$. Once decoded, the condition says "$B$ is bounded below," the
  analyst's lever for injectivity **and** closed range; combined with (c) it
  pins the range to exactly $(\ker B')^o$ and gives a bounded inverse.

## The Key Insight

Everything radiates from a single object: the bounded **bilinear form**
$$b:V\times W\to\mathbb R,\qquad b(v,w)=(Bv)(w),\qquad |b(v,w)|\le\|B\|\,\|v\|_V\|w\|_W.$$
$B$ and $B'$ are just its two *partial representations* — freeze the first slot
to get $B'w=b(\cdot,w)\in V'$, freeze the second to get $Bv=b(v,\cdot)\in W'$.
The symmetry of "freeze one slot" makes the double adjoint trivial. The inf-sup
bound is precisely "**$B$ is bounded below**," and bounded-below
$\Rightarrow$ injective $+$ closed range; part (c) then identifies that range as
$(\ker B')^o$. Reflexivity of the Hilbert spaces is the silent hypothesis that
makes the duality symmetric throughout.

## Complete Proof

Write $b(v,w):=(Bv)(w)$, a bounded bilinear form with
$|b(v,w)|\le\|B\|\,\|v\|_V\,\|w\|_W$, since $|(Bv)(w)|\le\|Bv\|_{W'}\|w\|_W\le
\|B\|\|v\|_V\|w\|_W$.

### Part (a) — $B'$ is continuous and $(B')'=B$

**$B'w$ is a bounded functional on $V$.** For fixed $w\in W$, define
$(B'w)(v):=(Bv)(w)=b(v,w)$. It is linear in $v$ (composition of the linear
$v\mapsto Bv$ with evaluation at $w$), and
$$|(B'w)(v)|=|b(v,w)|\le\|B\|\,\|w\|_W\,\|v\|_V,$$
so $B'w\in V'$ with $\|B'w\|_{V'}\le\|B\|\,\|w\|_W$.

**$B'$ is linear and continuous.** Linearity in $w$ is immediate from linearity
of $b$ in its second slot: $(B'(\alpha w_1+\beta w_2))(v)=b(v,\alpha w_1+\beta
w_2)=\alpha(B'w_1)(v)+\beta(B'w_2)(v)$. The bound above gives
$$\|B'\|_{\mathcal L(W,V')}\le\|B\|<\infty,$$
so $B':W\to V'$ is continuous.

**$(B')'=B$.** The adjoint recipe applied to $B':W\to V'$ — a continuous linear
map from a Hilbert space $W$ into the dual $V'$ of a Hilbert space — produces
$(B')':V\to W'$ defined by
$$\big((B')'v\big)(w):=(B'w)(v).$$
(Here we use $V''=V$ and $W''=W$: Hilbert spaces are reflexive, so the recipe
genuinely returns a map $V\to W'$.) But by the definition of $B'$,
$(B'w)(v)=(Bv)(w)$, hence
$$\big((B')'v\big)(w)=(Bv)(w)\quad\forall w\in W
\ \Longrightarrow\ (B')'v=Bv\quad\forall v\in V,$$
i.e. $(B')'=B$. (Symmetrically $\|B\|\le\|B'\|$, so in fact $\|B'\|=\|B\|$.)
$\blacksquare$

### Part (b) — $U^o$ is a closed subspace of $W'$

For each fixed $w\in W$, the **evaluation map** $\mathrm{ev}_w:W'\to\mathbb R$,
$\mathrm{ev}_w(f)=f(w)$, is linear and bounded:
$|\mathrm{ev}_w(f)|=|f(w)|\le\|f\|_{W'}\|w\|_W$. Now
$$U^o=\{f\in W':f(w)=0\ \forall w\in U\}=\bigcap_{w\in U}\ker(\mathrm{ev}_w).$$
Each $\ker(\mathrm{ev}_w)=\mathrm{ev}_w^{-1}(\{0\})$ is:
- a **subspace** (kernel of a linear map), and
- **closed** (preimage of the closed set $\{0\}$ under the continuous map
  $\mathrm{ev}_w$).

An arbitrary intersection of closed subspaces is a closed subspace, so $U^o$ is a
closed subspace of $W'$. $\blacksquare$

### Part (c) — $\overline{B(V)}=(\ker B')^o$

First unwind the kernel: $w\in\ker B'$ iff $B'w=0$ in $V'$ iff $(B'w)(v)=0$ for
all $v$, i.e.
$$\ker B'=\{w\in W:(Bv)(w)=0\ \ \forall v\in V\}.$$

**($\subseteq$) $B(V)\subseteq(\ker B')^o$, hence $\overline{B(V)}\subseteq(\ker
B')^o$.** Take $Bv\in B(V)$ and any $w\in\ker B'$. Then
$$(Bv)(w)=(B'w)(v)=0,$$
so $Bv$ annihilates $\ker B'$, i.e. $Bv\in(\ker B')^o$. By part (b),
$(\ker B')^o$ is closed; containing $B(V)$, it contains $\overline{B(V)}$.

**($\supseteq$) $(\ker B')^o\subseteq\overline{B(V)}$.** Suppose, for
contradiction, that some $f\in(\ker B')^o$ satisfies $f\notin\overline{B(V)}$.
Since $\overline{B(V)}$ is a closed subspace of the Banach space $W'$, the
Hahn–Banach separation theorem provides $\Phi\in W''$ with
$$\Phi|_{\overline{B(V)}}=0\qquad\text{and}\qquad\Phi(f)\ne 0.$$
Because $W$ is a Hilbert space, it is reflexive, so $W''=W$ and $\Phi$ is
evaluation at some $w_0\in W$: $\Phi(g)=g(w_0)$ for all $g\in W'$. Now:
- $\Phi$ vanishes on $B(V)$ means $(Bv)(w_0)=0$ for all $v$, i.e. $(B'w_0)(v)=0$
  for all $v$, i.e. $B'w_0=0$, so $w_0\in\ker B'$.
- $f\in(\ker B')^o$ then forces $f(w_0)=0$, i.e. $\Phi(f)=0$.

This contradicts $\Phi(f)\ne 0$. Hence no such $f$ exists, giving
$(\ker B')^o\subseteq\overline{B(V)}$.

Combining the inclusions, $\overline{B(V)}=(\ker B')^o$. $\blacksquare$

### Part (d) — Under the inf-sup condition, $B:V\xrightarrow{\ \sim\ }(\ker B')^o$

**Decode the hypothesis.** For $Bv\ne 0$,
$$\sup_{w\ne 0}\frac{(Bv)(w)}{\|w\|_W}=\sup_{w\ne 0}\frac{|(Bv)(w)|}{\|w\|_W}=\|Bv\|_{W'},$$
the first equality because replacing $w$ by $-w$ flips the sign, so the supremum
of the signed quotient equals that of its absolute value (and both sides are $0$
when $Bv=0$). Thus the assumption is the **inf-sup / bounded-below** condition
$$\|Bv\|_{W'}\ \ge\ \alpha\,\|v\|_V\qquad\forall v\in V,\quad\alpha>0. \tag{IS}$$

**Step 1: $B$ is injective.** If $Bv=0$ then $0=\|Bv\|_{W'}\ge\alpha\|v\|_V$, so
$\|v\|_V=0$, i.e. $v=0$.

**Step 2: $B$ has closed range.** Let $Bv_n\to g$ in $W'$. Then $(Bv_n)$ is
Cauchy, and (IS) applied to $v_n-v_m$ gives
$$\|v_n-v_m\|_V\le\tfrac1\alpha\|Bv_n-Bv_m\|_{W'}\xrightarrow[n,m\to\infty]{}0,$$
so $(v_n)$ is Cauchy in the complete space $V$ and converges to some $v$. By
continuity of $B$, $Bv_n\to Bv$, hence $g=Bv\in B(V)$. Therefore $B(V)$ is
closed.

**Step 3: identify the range.** Since $B(V)$ is closed,
$\overline{B(V)}=B(V)$, and part (c) gives
$$B(V)=\overline{B(V)}=(\ker B')^o.$$
With Step 1, $B:V\to(\ker B')^o$ is a continuous **linear bijection**.

**Step 4: bounded inverse.** From (IS), $\|v\|_V\le\tfrac1\alpha\|Bv\|_{W'}$ for
all $v$, i.e. for $g=Bv\in(\ker B')^o$,
$$\|B^{-1}g\|_V\le\tfrac1\alpha\|g\|_{W'},$$
so $B^{-1}:(\ker B')^o\to V$ is bounded with $\|B^{-1}\|\le 1/\alpha$.
(Equivalently: $(\ker B')^o$ is a closed subspace of $W'$, hence Banach, and a
continuous linear bijection between Banach spaces has bounded inverse by the open
mapping theorem.)

Therefore $B$ is an **isomorphism** of $V$ onto $(\ker B')^o$, with
$\alpha\|v\|_V\le\|Bv\|_{W'}\le\|B\|\,\|v\|_V$. $\blacksquare$

## What Connects

**To the closed range theorem.** Part (c) is exactly the Hilbert-space case of
Banach's closed range theorem identity $\overline{\operatorname{ran}B}=(\ker
B^*)^\perp$ (here written with annihilators in the dual). The four standard
statements — $\operatorname{ran}B$ closed, $\operatorname{ran}B'$ closed,
$\operatorname{ran}B=(\ker B')^o$, $\operatorname{ran}B'=(\ker B)^o$ — are all
equivalent; part (d)'s inf-sup condition is one concrete sufficient hypothesis
that makes $\operatorname{ran}B$ closed.

**To Babuška–Brezzi / LBB and mixed finite elements.** Condition (IS) is the
**inf-sup (Ladyzhenskaya–Babuška–Brezzi) condition**:
$\inf_{v}\sup_{w} b(v,w)/(\|v\|\|w\|)\ge\alpha>0$. It is the cornerstone of
well-posedness for saddle-point problems (Stokes flow, mixed formulations of
elliptic PDEs, Lagrange-multiplier methods). The discrete analogue — the
*uniform* inf-sup condition on finite-element pairs $(V_h,W_h)$ — is precisely
what separates stable elements (Taylor–Hood) from unstable ones (equal-order
$P_1$–$P_1$ for Stokes).

**To the Banach–Nečas–Babuška theorem.** Parts (c)+(d) together are the core of
the BNB theorem: a bounded bilinear form is well-posed iff it satisfies an
inf-sup condition *and* a nondegeneracy condition on the second variable. The
range being all of $(\ker B')^o$ is what makes solvability hold exactly on the
compatible right-hand sides (those annihilating $\ker B'$).

**To the adjoint as a bilinear pairing.** Viewing $B,B'$ as the two slot-freezes
of $b(v,w)$ is the cleanest way to see why $\|B\|=\|B'\|$ and $(B')'=B$, and it
generalizes verbatim to non-reflexive Banach spaces *except* for the
double-adjoint identity, which is precisely where reflexivity of the Hilbert
spaces is used.

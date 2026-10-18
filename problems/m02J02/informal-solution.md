<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16; revised 2026-10-18 (Hermite functions are not H^1-orthogonal; bases in (b),(c) now come from Gram–Schmidt) -->


# APM m02J02: Bases for $H_0^1(\Omega)$ — discrete vs. continuous spectrum

## Why It's Hard

The three domains look similar but are governed by a single dichotomy: whether the
Dirichlet Laplacian $-d^2/dx^2$ on $\Omega$ has **discrete** or **continuous** spectrum.
On the bounded interval $(0,1)$ the resolvent is compact, so there is a complete set of
$L^2$ eigenfunctions — the sines — which double as an explicit orthogonal basis of
$H^1_0$. On the unbounded domains $(0,\infty)$ and $\mathbb R$ the spectrum is continuous,
so **no $L^2$ eigenfunctions exist** and there is no "eigenbasis"; the trap is to conclude
there is no basis at all. In fact each $H^1_0(\Omega)$ is a *separable* Hilbert space, so
it always has a countable orthonormal basis — one just has to produce one from a different
complete family, and to remember that on all of $\mathbb R$, $H^1_0(\mathbb R)=H^1(\mathbb R)$.

A second trap is to take the Hermite functions themselves as that basis. They are complete
in $H^1(\mathbb R)$ but **not orthogonal** in the $H^1$ inner product, and in their natural
order they are not even a Schauder basis of $H^1(\mathbb R)$ (see the Remark at the end). An
orthonormal basis is obtained by applying Gram–Schmidt to them in the $H^1$ inner product.

## The Key Insight

A separable Hilbert space has a countable orthonormal basis, obtained by Gram–Schmidt from
any countable linearly independent set whose span is dense. All three $H^1_0(\Omega)$ are
separable. The task is to name such a set:
- **(a)** bounded $\Rightarrow$ discrete spectrum $\Rightarrow$ the eigenfunctions
  $\{\sin(n\pi x)\}_{n\ge1}$ are already orthogonal in $H^1_0$, and complete.
- **(b),(c)** unbounded $\Rightarrow$ continuous spectrum $\Rightarrow$ no eigenbasis. Use the
  Hermite functions (eigenfunctions of $-d^2/dx^2+x^2$, which *does* have compact resolvent
  on $\mathbb R$): all of them on $\mathbb R$, the *odd* ones (which vanish at $0$) on
  $(0,\infty)$. Their span is dense because Schwartz functions are dense in $H^1$ and the
  Hermite expansion of a Schwartz function converges in $H^1$. Gram–Schmidt in the $H^1$
  inner product then gives the orthonormal basis.

## Complete Proof

Throughout, $\mathcal D(\Omega)=C_c^\infty(\Omega)$, $H^1(\Omega)$ carries the usual inner
product $(u,v)_{H^1}=\int_\Omega (u^{\prime}v^{\prime}+uv)\,dx$, and
$H^1_0(\Omega)=\overline{\mathcal D(\Omega)}^{\,\|\cdot\|_{H^1}}$. Each $H^1_0(\Omega)$ is a
closed subspace of the separable space $H^1(\Omega)$, hence is itself a **separable**
Hilbert space. "Basis" below means an orthonormal (or orthogonal) basis of this Hilbert
space: every element is the norm-convergent sum of its expansion.

### (a) $\Omega=(0,1)$: the sine basis (discrete spectrum)

The Dirichlet eigenvalue problem $-u^{\prime\prime}=\lambda u$, $u(0)=u(1)=0$ has eigenpairs
$$
e_n(x)=\sin(n\pi x),\qquad \lambda_n=(n\pi)^2,\qquad n=1,2,3,\dots
$$
These are the eigenfunctions of a self-adjoint operator with **compact resolvent** (the
interval is bounded), so $\{e_n\}$ is a complete orthogonal system in $L^2(0,1)$. For
$u\in H^1_0(0,1)$, integration by parts (first for $u\in\mathcal D(0,1)$, then by density)
gives $\int_0^1 u^{\prime}e_n^{\prime}\,dx=\lambda_n\int_0^1 ue_n\,dx$, hence
$$
(u,e_n)_{H^1}=(1+\lambda_n)\int_0^1 ue_n\,dx .
$$
Taking $u=e_m$ shows the $e_n$ are orthogonal in $H^1$. If $u\in H^1_0(0,1)$ is
$H^1$-orthogonal to all $e_n$, then $\int_0^1 ue_n=0$ for all $n$, so $u=0$ in $L^2$, hence
$u=0$. Therefore
$$
\boxed{\{\sin(n\pi x)\}_{n\ge1}}
$$
is an orthogonal basis of $H^1_0(0,1)$; normalized, $\Big\{\big(\tfrac{1+(n\pi)^2}{2}\big)^{-1/2}
\sin(n\pi x)\Big\}_{n\ge1}$ is orthonormal. (The same family is orthogonal for the equivalent
inner product $\int_0^1u^{\prime}v^{\prime}$ given by the Poincaré inequality, with normalization
$\tfrac{\sqrt2}{n\pi}\sin(n\pi x)$.)

### Hermite functions in $H^1(\mathbb R)$

Let $h_m(x)=(2^m m!\sqrt\pi)^{-1/2}H_m(x)e^{-x^2/2}$, $m\ge0$, be the Hermite functions. They
are the eigenfunctions of $\mathcal H=-d^2/dx^2+x^2$, $\mathcal Hh_m=(2m+1)h_m$, they form an
orthonormal basis of $L^2(\mathbb R)$, they lie in the Schwartz class $\mathcal S(\mathbb R)$,
and $h_m$ has the parity of $m$. They satisfy
$$
h_m^{\prime}=\sqrt{\tfrac m2}\,h_{m-1}-\sqrt{\tfrac{m+1}2}\,h_{m+1}. \tag{1}
$$

**They are not $H^1$-orthogonal.** By (1),
$$
(h_m,h_k)_{H^1}=\delta_{mk}+(h_m^{\prime},h_k^{\prime})_{L^2},\qquad
\|h_m\|_{H^1}^2=m+\tfrac32,\qquad
(h_m,h_{m+2})_{H^1}=-\tfrac12\sqrt{(m+1)(m+2)}\neq0 .
$$
(Functions of opposite parity are $H^1$-orthogonal, and so are $h_m,h_k$ with $|m-k|\ge3$.)

**Lemma.** For $\varphi\in\mathcal S(\mathbb R)$ with $c_m=(\varphi,h_m)_{L^2}$, the series
$\sum_m c_mh_m$ converges absolutely in $H^1(\mathbb R)$, and its sum is $\varphi$.

*Proof.* $\mathcal H$ is symmetric on $\mathcal S$ and maps $\mathcal S$ to itself, so
$c_m=(2m+1)^{-2}(\mathcal H^2\varphi,h_m)_{L^2}$ and $|c_m|\le(2m+1)^{-2}\|\mathcal H^2\varphi\|_{L^2}$.
Hence $\sum_m|c_m|\,\|h_m\|_{H^1}\le\|\mathcal H^2\varphi\|_{L^2}\sum_m\sqrt{m+3/2}\,(2m+1)^{-2}<\infty$,
so the series converges in $H^1$. Its $H^1$-limit is also its $L^2$-limit, which is $\varphi$
because $\{h_m\}$ is an orthonormal basis of $L^2$. $\square$

### (b) $\Omega=(0,\infty)$: no eigenbasis; Gram–Schmidt on the odd Hermite functions

Here $-d^2/dx^2$ with $u(0)=0$ has **continuous spectrum** $[0,\infty)$: the "eigen"
solutions $\sin(kx)$ are not in $L^2(0,\infty)$, so there is no orthonormal basis of
eigenfunctions. Nonetheless $H^1_0(0,\infty)$ is separable, so a countable basis exists.
Let $g_n=h_{2n+1}|_{(0,\infty)}$, $n\ge0$.

*Membership.* $h_{2n+1}$ is odd, smooth and rapidly decaying, so $g_n\in H^1(0,\infty)$,
$g_n$ is continuous on $[0,\infty)$ and $g_n(0)=0$. A function in $H^1(0,\infty)$ that is
continuous up to $0$ and vanishes there lies in $H^1_0(0,\infty)$ (e.g. Brezis, *Functional
Analysis*, Thm. 8.12), so $g_n\in H^1_0(0,\infty)$.

*Independence.* For odd $u,v$ the integrands $uv$ and $u^{\prime}v^{\prime}$ are even, so
$(g_n,g_k)_{L^2(0,\infty)}=\tfrac12\delta_{nk}$. The $g_n$ are $L^2$-orthogonal and nonzero,
hence linearly independent. (Their $H^1(0,\infty)$ Gram matrix is half that of the odd
$h_m$ in $H^1(\mathbb R)$, so it is not diagonal.)

*Density of the span.* Let $\varphi\in\mathcal D(0,\infty)$ and let $\tilde\varphi$ be its odd
extension; since $\operatorname{supp}\varphi$ stays away from $0$, $\tilde\varphi\in\mathcal
D(\mathbb R)\subset\mathcal S(\mathbb R)$. By parity $(\tilde\varphi,h_{2n})_{L^2}=0$, so the
Lemma gives $\tilde\varphi=\sum_n c_{2n+1}h_{2n+1}$ in $H^1(\mathbb R)$. Restriction to
$(0,\infty)$ is bounded $H^1(\mathbb R)\to H^1(0,\infty)$, so $\varphi=\sum_n c_{2n+1}g_n$ in
$H^1(0,\infty)$. Thus $\mathcal D(0,\infty)$, and hence $H^1_0(0,\infty)$, lies in the closed
span of $\{g_n\}$.

Applying Gram–Schmidt to $g_0,g_1,g_2,\dots$ in the $H^1(0,\infty)$ inner product therefore
produces an orthonormal basis:
$$
\boxed{\ \text{the }H^1\text{-Gram–Schmidt orthonormalization of }\{\,h_{2n+1}|_{(0,\infty)}\,\}_{n\ge0}\ }
$$
Each basis element is $p(x)e^{-x^2/2}$ for an odd polynomial $p$.

### (c) $\Omega=\mathbb R$: $H^1_0=H^1$; Gram–Schmidt on the Hermite functions

On the whole line there is no boundary, and $C_c^\infty(\mathbb R)$ is dense in
$H^1(\mathbb R)$, so
$$
H^1_0(\mathbb R)=H^1(\mathbb R).
$$
Again $-d^2/dx^2$ has continuous spectrum $[0,\infty)$ (no $L^2$ eigenfunctions), so there is
no eigenbasis of the Laplacian. The Hermite functions $\{h_m\}_{m\ge0}$ are linearly
independent (they are $L^2$-orthonormal), and their span is dense in $H^1(\mathbb R)$: it
contains in its closure every $\varphi\in\mathcal D(\mathbb R)\subset\mathcal S(\mathbb R)$ by
the Lemma, and $\mathcal D(\mathbb R)$ is dense. Gram–Schmidt in the $H^1(\mathbb R)$ inner
product therefore produces an orthonormal basis:
$$
\boxed{\ \text{the }H^1\text{-Gram–Schmidt orthonormalization of }\{h_m\}_{m\ge0}\ }
$$
Since even and odd functions are $H^1$-orthogonal, the process runs separately on
$h_0,h_2,h_4,\dots$ and on $h_1,h_3,h_5,\dots$; each basis element is $p(x)e^{-x^2/2}$ for a
polynomial $p$ of the same degree and parity as the $h_m$ it replaces.

### Remark: why not the Hermite functions themselves

In their natural order the $h_m$ are not a Schauder basis of $H^1(\mathbb R)$, so the
orthonormalization above is needed and not cosmetic. Write $u=\sum c_mh_m\in H^1(\mathbb R)$,
$S_Nu=\sum_{m\le N}c_mh_m$, and $d_k=(u^{\prime},h_k)_{L^2}$. Using (1),
$$
\|(u-S_Nu)^{\prime}\|_{L^2}^2=\sum_{k\ge N+2}|d_k|^2+\tfrac{N+1}2|c_{N+1}|^2+\tfrac{N+2}2|c_{N+2}|^2 ,
$$
so $S_Nu\to u$ in $H^1$ exactly when $\sqrt N\,c_N\to0$. Choosing $c_m=s_m/\sqrt m$ with
$0\le s_m\le1$ equal to $1$ at very sparse indices $N_j$ and ramping linearly to $0$ over
$j^2$ steps on each side keeps $(c_m)$ and $(d_k)$ in $\ell^2$, so $u\in H^1$, while
$\sqrt{N_j}\,c_{N_j}=1$ for all $j$. (Such $u$ has $\int x^2u^2=\infty$, which $H^1$ permits.)

The organizing principle is still **compactness of the resolvent**: it holds for
$-d^2/dx^2$ on a *bounded* domain (giving the sine eigenbasis in (a), orthogonal in $H^1_0$
because the $H^1_0$ form is diagonal on Dirichlet eigenfunctions), fails for $-d^2/dx^2$ on
unbounded domains (continuous spectrum, no eigenbasis in (b),(c)), and is *restored* by the
confining potential $x^2$. The Hermite eigenfunctions of $-d^2/dx^2+x^2$ supply a complete
family, but they diagonalize $\int(u^{\prime 2}+x^2u^2)$, not the $H^1$ form
$\int(u^{\prime 2}+u^2)$, which is why Gram–Schmidt is needed. The one structural difference
between (b) and (c) is the boundary: on $\mathbb R$ there is none, so $H^1_0=H^1$; on
$(0,\infty)$, $H^1_0$ is the proper (trace-zero) subspace, which is why only the *odd*
Hermite functions — those vanishing at the origin — appear.

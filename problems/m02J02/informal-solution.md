<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m02J02: Bases for H₀¹(Ω) — discrete vs. continuous spectrum

## Why It's Hard

The three domains look similar but are governed by a single dichotomy: whether the
Dirichlet Laplacian $-d^2/dx^2$ on $\Omega$ has **discrete** or **continuous** spectrum.
On the bounded interval $(0,1)$ the resolvent is compact, so there is a complete set of
$L^2$ eigenfunctions — the sines — which double as an explicit orthogonal basis of
$H^1_0$. On the unbounded domains $(0,\infty)$ and $\mathbb R$ the spectrum is continuous,
so **no $L^2$ eigenfunctions exist** and there is no "eigenbasis"; the trap is to conclude
there is no basis at all. In fact each $H^1_0(\Omega)$ is a *separable* Hilbert space, so
it always has a countable orthonormal basis — one just has to exhibit one from a different
complete family (Hermite functions), and to remember that on all of $\mathbb R$,
$H^1_0(\mathbb R)=H^1(\mathbb R)$.

## The Key Insight

A separable Hilbert space has a countable orthonormal basis; all three $H^1_0(\Omega)$ are
separable. The *natural* basis depends on the spectrum of the Dirichlet Laplacian:
- **(a)** bounded $\Rightarrow$ discrete spectrum $\Rightarrow$ eigenfunctions
  $\{\sin(n\pi x)\}_{n\ge1}$ (a basis of both $L^2$ and $H^1_0$).
- **(b),(c)** unbounded $\Rightarrow$ continuous spectrum $\Rightarrow$ no eigenbasis, but
  a countable basis still exists: take Hermite functions (eigenfunctions of $-d^2/dx^2+x^2$,
  which *does* have compact resolvent on $\mathbb R$) — all of them on $\mathbb R$, and the
  *odd* ones (which vanish at $0$) on $(0,\infty)$.

## Complete Proof

Throughout, $\mathcal D(\Omega)=C_c^\infty(\Omega)$ and $H^1_0(\Omega)=\overline{\mathcal
D(\Omega)}^{\,\|\cdot\|_{H^1}}$. Each $H^1_0(\Omega)$ is a closed subspace of the separable
space $H^1(\Omega)$, hence is itself a **separable** Hilbert space, and therefore possesses
a countable orthonormal basis (Gram–Schmidt applied to any countable total subset). The
task is to identify a concrete one in each case.

### (a) $\Omega=(0,1)$: the sine basis (discrete spectrum)

The Dirichlet eigenvalue problem $-u''=\lambda u$, $u(0)=u(1)=0$ has eigenpairs
$$
e_n(x)=\sin(n\pi x),\qquad \lambda_n=(n\pi)^2,\qquad n=1,2,3,\dots
$$
These are the eigenfunctions of a self-adjoint operator with **compact resolvent** (the
interval is bounded), so $\{e_n\}$ is a complete orthogonal system in $L^2(0,1)$. They are
orthogonal *also in the $H^1_0$ inner product* $(u,v)_{H^1_0}=\int_0^1 u'v'\,dx$ (an inner
product on $H^1_0(0,1)$ by the Poincaré inequality), since
$$
\int_0^1 e_n'e_m'\,dx=\lambda_n\!\int_0^1 e_ne_m\,dx=0\quad(n\neq m).
$$
Completeness in $H^1_0$ follows from completeness in $L^2$: if $u\in H^1_0(0,1)$ is
$H^1_0$-orthogonal to all $e_n$, then $\int u'e_n'=\lambda_n\int ue_n=0$ forces $\int
ue_n=0$ for all $n$, so $u=0$ in $L^2$, hence $u=0$. Therefore
$$
\boxed{\{\sin(n\pi x)\}_{n\ge1}}
$$
is an orthogonal basis of $H^1_0(0,1)$; normalized, $\Big\{\dfrac{\sqrt2}{n\pi}\sin(n\pi
x)\Big\}_{n\ge1}$ is orthonormal in $H^1_0$ (since $\|\sin(n\pi
x)\|_{H^1_0}^2=\int_0^1(n\pi\cos n\pi x)^2=\tfrac{(n\pi)^2}{2}$).

### (b) $\Omega=(0,\infty)$: no eigenbasis, but an explicit Hermite-odd basis

Here $-d^2/dx^2$ with $u(0)=0$ has **continuous spectrum** $[0,\infty)$: the "eigen"
solutions $\sin(kx)$ are not in $L^2(0,\infty)$, so there is no orthonormal basis of
eigenfunctions. Nonetheless $H^1_0(0,\infty)$ is separable, so a countable basis exists.
An explicit one comes from the **Hermite functions** $h_m(x)=c_m H_m(x)e^{-x^2/2}$
(eigenfunctions of $-d^2/dx^2+x^2$ on $\mathbb R$, an operator with compact resolvent),
which form an orthonormal basis of $L^2(\mathbb R)$ and lie in $H^1(\mathbb R)$. The
**odd** Hermite functions $h_{2n+1}$ ($n\ge0$) are odd, hence
$$
h_{2n+1}(0)=0\quad\text{and}\quad h_{2n+1}\in H^1_0(0,\infty)\ \text{(after restriction)},
$$
they decay rapidly (compact-support density gives $h_{2n+1}\in\overline{\mathcal
D(0,\infty)}$), and by the even/odd decomposition $L^2(\mathbb R)=L^2_{\rm even}\oplus
L^2_{\rm odd}$ the restrictions $\{h_{2n+1}|_{(0,\infty)}\}_{n\ge0}$ are a complete
orthogonal system in $L^2(0,\infty)$. By the same eigenfunction/Gram–Schmidt reasoning as
in (a) they yield a countable orthogonal basis of $H^1_0(0,\infty)$:
$$
\boxed{\{\,h_{2n+1}|_{(0,\infty)}\,\}_{n\ge0}}
$$
(Equivalently one may take Gram–Schmidt in $H^1_0$ of the total, independent set
$\{x^k e^{-x}\}_{k\ge1}$, all of which vanish at $0$, decay, and lie in $H^1_0(0,\infty)$;
relatives of the associated Laguerre functions.)

### (c) $\Omega=\mathbb R$: $H^1_0=H^1$ with the Hermite basis

On the whole line there is no boundary, and $C_c^\infty(\mathbb R)$ is dense in
$H^1(\mathbb R)$, so
$$
H^1_0(\mathbb R)=H^1(\mathbb R).
$$
Again $-d^2/dx^2$ has continuous spectrum $[0,\infty)$ (no $L^2$ eigenfunctions), so no
eigenbasis of the Laplacian; but the **Hermite functions** $\{h_m\}_{m\ge0}$ (eigenfunctions
of the harmonic oscillator $-d^2/dx^2+x^2$, eigenvalues $2m+1$) form an orthonormal basis
of $L^2(\mathbb R)$ and, being a complete system inside the Schwartz class, are total in
$H^1(\mathbb R)$. They are mutually orthogonal in the $H^1$ inner product as well
($\int(h_m'h_k'+h_mh_k)$ is diagonalized along with $-d^2/dx^2+x^2$). Hence
$$
\boxed{\{h_m\}_{m\ge0}=\{c_m H_m(x)e^{-x^2/2}\}_{m\ge0}}
$$
is an (orthogonal, after normalization orthonormal) basis of $H^1_0(\mathbb R)=H^1(\mathbb R)$.

### Remark

The organizing principle is **compactness of the resolvent**: it holds for $-d^2/dx^2$ on
a *bounded* domain (giving the sine eigenbasis in (a)), fails for $-d^2/dx^2$ on unbounded
domains (continuous spectrum, no eigenbasis in (b),(c)), but is *restored* by adding the
confining potential $x^2$, whose eigenfunctions (Hermite) supply explicit bases for the
unbounded cases. The one structural difference between (b) and (c) is the boundary: on
$\mathbb R$ there is none, so $H^1_0=H^1$; on $(0,\infty)$, $H^1_0$ is the proper
(trace-zero) subspace, which is exactly why only the *odd* Hermite functions — those
vanishing at the origin — appear.

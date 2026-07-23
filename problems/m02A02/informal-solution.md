<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m02A02: The periodic Poisson problem — Poincaré–Wirtinger and well-posedness on the torus

## Why It's Hard

This is the Dirichlet-energy problem on the torus $\Omega=[0,1]^2$ (periodic boundary
conditions), where the Laplacian has a nontrivial kernel — the **constants** — so nothing
is well-posed until that one degree of freedom is removed by the mean-zero normalization
$\int_\Omega u=0$. The crux is the Poincaré–Wirtinger inequality (b): the gradient norm
controls the $L^2$ norm *only* on mean-zero functions, because the constant mode is
exactly what $\nabla$ annihilates. Once that coercivity is in hand, Lax–Milgram/Riesz
gives existence-uniqueness (c), and the equivalence with $-\Delta u=f$ (d) carries a
compatibility condition $\int f=0$ that is the Fredholm shadow of the same kernel.

## The Key Insight

- **(a)** $H^1_{P,0}=\ker\ell$ for the bounded functional $\ell(u)=\int_\Omega u$, so it is
  a closed subspace of the Hilbert space $H^1_P$, hence Hilbert.
- **(b)** Fourier: $u=\sum_k\hat u_k e^{2\pi i k\cdot x}$, $\hat u_0=0$ (mean zero), and
  $\|\nabla u\|^2=4\pi^2\sum_{k\neq0}|k|^2|\hat u_k|^2\ge4\pi^2\sum_{k\neq0}|\hat u_k|^2
  =4\pi^2\|u\|^2$ (since $|k|^2\ge1$ for $k\neq0$).
- **(c)** By (b), $a(w,v)=\int\nabla w\cdot\nabla v$ is coercive on $H^1_{P,0}$; it is a
  symmetric, bounded, coercive form, so the affine variational problem has a unique
  solution (Lax–Milgram / Riesz).
- **(d)** Integration by parts with periodic boundary terms cancelling shows the weak
  problem is $-\Delta u=f$ in $\mathcal D'$, valid precisely when $\int_\Omega f=0$
  (forced by integrating the equation on the torus).

## Complete Proof

$\Omega=[0,1]^2$, $|\Omega|=1$; $H^1_P(\Omega)$ is the periodic $H^1$ space and
$H^1_{P,0}=\{u\in H^1_P:\int_\Omega u=0\}$, both with the $H^1$ inner product $\langle
u,v\rangle_{H^1}=\int_\Omega(uv+\nabla u\cdot\nabla v)$.

### (a) $H^1_{P,0}$ is a Hilbert space

$H^1_P$ is a Hilbert space (the completion of $C^\infty_P$ in $H^1$ is a closed subspace
of $H^1(\Omega)$). The map $\ell(u)=\int_\Omega u\,dx$ is linear and bounded on $H^1$: by
Cauchy–Schwarz, $|\ell(u)|\le|\Omega|^{1/2}\|u\|_{L^2}=\|u\|_{L^2}\le\|u\|_{H^1}$. Hence
$H^1_{P,0}=\ker\ell$ is the preimage of $\{0\}$ under a continuous map, so it is a
**closed** subspace of $H^1_P$. A closed subspace of a Hilbert space, with the restricted
inner product, is complete, hence itself a Hilbert space. $\quad\checkmark$

### (b) Poincaré–Wirtinger inequality

It suffices to prove it for $u\in C^\infty_P$ with $\int_\Omega u=0$ and pass to the limit
(both sides are continuous in the $H^1$ norm, and such $u$ are dense in $H^1_{P,0}$).
Expand in Fourier series on the torus,
$$
u(x)=\sum_{k\in\mathbb Z^2}\hat u_k\,e^{2\pi i k\cdot x},\qquad
\hat u_0=\int_\Omega u\,dx=0 .
$$
By Parseval, $\|u\|_{L^2}^2=\sum_{k}|\hat u_k|^2$, and since $\widehat{\nabla u}_k=2\pi i\,
k\,\hat u_k$,
$$
\|\nabla u\|_{L^2}^2=\sum_k|2\pi k|^2|\hat u_k|^2=4\pi^2\sum_{k\neq0}|k|^2|\hat u_k|^2 .
$$
For $k\in\mathbb Z^2$ with $k\neq0$ we have $|k|^2\ge1$, so
$$
\|\nabla u\|_{L^2}^2\ge 4\pi^2\sum_{k\neq0}|\hat u_k|^2=4\pi^2\sum_{k}|\hat u_k|^2
=4\pi^2\|u\|_{L^2}^2 ,
$$
where the middle equality used $\hat u_0=0$. Therefore
$$
\int_\Omega|u|^2\,dx\le\frac{1}{4\pi^2}\int_\Omega|\nabla u|^2\,dx,
$$
i.e. the claim holds with $C=\tfrac1{4\pi^2}$. $\quad\checkmark$

### (c) Unique solution of the variational problem

Seek $u\in u_0+H^1_{P,0}$, i.e. $u=u_0+w$ with $w\in H^1_{P,0}$ unknown, such that
$\int_\Omega\nabla u\cdot\nabla v=\int_\Omega fv$ for all $v\in H^1_{P,0}$. Substituting,
this is
$$
a(w,v):=\int_\Omega\nabla w\cdot\nabla v\,dx=\underbrace{\int_\Omega fv-\int_\Omega\nabla u_0\cdot\nabla v}_{=:L(v)}\qquad\forall v\in H^1_{P,0}.
$$
On the Hilbert space $H^1_{P,0}$:
- $a$ is **bilinear, symmetric, bounded**: $|a(w,v)|\le\|\nabla w\|_{L^2}\|\nabla v\|_{L^2}
  \le\|w\|_{H^1}\|v\|_{H^1}$.
- $a$ is **coercive**: by (b), $\|v\|_{H^1}^2=\|v\|_{L^2}^2+\|\nabla v\|_{L^2}^2\le
  (C+1)\|\nabla v\|_{L^2}^2=(C+1)\,a(v,v)$, so $a(v,v)\ge\frac1{C+1}\|v\|_{H^1}^2$.
- $L$ is a **bounded linear functional**: $|L(v)|\le\|f\|_{L^2}\|v\|_{L^2}+\|\nabla u_0\|_{L^2}
  \|\nabla v\|_{L^2}\le\big(\|f\|_{L^2}+\|u_0\|_{H^1}\big)\|v\|_{H^1}$.

By the Lax–Milgram theorem (here $a$ is symmetric, so this is just the Riesz
representation theorem for the equivalent inner product $a(\cdot,\cdot)$), there is a
unique $w\in H^1_{P,0}$ with $a(w,v)=L(v)$ for all $v$. Then $u=u_0+w$ is the unique
solution of the variational problem. $\quad\blacksquare$

### (d) Equivalence with $-\Delta u=f$

**Weak $\Leftarrow$ strong.** Suppose $u\in u_0+H^1_{P,0}$ satisfies $-\Delta u=f$ in the
distributional sense on the torus. For $v\in H^1_{P,0}$ (approximated by $C^\infty_P$
mean-zero functions), integrate by parts:
$$
\int_\Omega(-\Delta u)\,v=\int_\Omega\nabla u\cdot\nabla v-\int_{\partial\Omega}\frac{\partial u}{\partial n}\,v .
$$
By **periodicity**, the boundary integrals over opposite edges of the square cancel (equal
traces of $u,v$ and their normal derivatives, with opposite outward normals), so the
boundary term vanishes and $\int_\Omega\nabla u\cdot\nabla v=\int_\Omega fv$ — the weak
form. (Integrating $-\Delta u=f$ over $\Omega$, the left side is $0$ by periodicity, so
necessarily $\int_\Omega f=0$.)

**Weak $\Rightarrow$ strong.** Suppose $u$ solves the weak problem. For an arbitrary
periodic test function $\varphi\in C^\infty_P$, write $\varphi=(\varphi-\bar\varphi)+
\bar\varphi$ with $\bar\varphi=\int_\Omega\varphi$; then $\varphi-\bar\varphi\in
H^1_{P,0}$ and $\nabla\varphi=\nabla(\varphi-\bar\varphi)$, so
$$
\int_\Omega\nabla u\cdot\nabla\varphi=\int_\Omega\nabla u\cdot\nabla(\varphi-\bar\varphi)
=\int_\Omega f(\varphi-\bar\varphi)=\int_\Omega f\varphi-\bar\varphi\int_\Omega f .
$$
Thus $\langle-\Delta u,\varphi\rangle=\int_\Omega\nabla u\cdot\nabla\varphi=\int_\Omega
(f-\bar f)\varphi$ for all periodic $\varphi$ (where $\bar f=\int_\Omega f$, using
$\int_\Omega\bar\varphi\,(\cdot)$ bookkeeping), i.e.
$$
-\Delta u=f-\bar f\quad\text{in }\mathcal D'(\text{torus}).
$$
Hence the weak problem is exactly $-\Delta u=f$ **under the compatibility condition
$\int_\Omega f=0$** (equivalently $\bar f=0$); this condition is not a restriction but the
necessary solvability requirement, since $\int_\Omega(-\Delta u)=0$ forces $\int_\Omega
f=0$ for *any* periodic solution. The boundary condition of the BVP is the periodicity
(built into $H^1_P$), and the constraint $u\in u_0+H^1_{P,0}$ fixes the otherwise-free
additive constant (the kernel of $-\Delta$). $\quad\blacksquare$

### Remark

The whole problem is the Fredholm theory of $-\Delta$ on the torus: $\ker(-\Delta)=$
constants, so (i) solutions are unique only after killing the constant (the mean-zero
normalization, part c), and (ii) solutions exist only for right-hand sides orthogonal to
the kernel, i.e. $\int_\Omega f=0$ (part d). Poincaré–Wirtinger (b) is precisely the
statement that $-\Delta$ is *coercive* on the orthogonal complement of its kernel, with
spectral gap $4\pi^2=(2\pi)^2$ — the smallest nonzero eigenvalue $|2\pi k|^2$ — which is
why the optimal constant is $C=1/4\pi^2$.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99J06: The Galerkin method for $u-u''=f$ on $H_0^1(0,1)$ — weak formulation, finite-dimensional solvability, a priori bound, and convergence

## Why It's Hard

The problem walks through the entire **Galerkin (finite-element) existence theory** for a model elliptic boundary-value problem, and each part is a different pillar:

- **(a)/(b)** require fluency with $H_0^1$: what its elements *are* (the 1D Sobolev embedding $H^1\hookrightarrow C[0,1]$ is what makes the boundary conditions $u(0)=u(1)=0$ meaningful), and the **weak$\,\leftrightarrow\,$strong equivalence**, which needs distributional integration by parts *and* an elliptic-regularity bootstrap ($u''=u-f\in L^2\Rightarrow u\in H^2$).
- **(c)** the finite-dimensional solvability hinges on the hint "why is uniqueness sufficient?" — the linear-algebra fact that an **injective** linear map on a finite-dimensional space is automatically **surjective**. Coercivity gives injectivity in one line; finite-dimensionality converts it to existence.
- **(d)** the **a priori bound** $\|u_n\|\le\|f\|$ is the crux of the whole method, and the clever step is *testing the equation against the solution itself*. Boundedness then yields a weak limit by Hilbert-space weak compactness — but only along a **subsequence**, a subtlety one must acknowledge.
- **(e)** passing to the limit needs two ingredients working together: weak convergence kills the linear functional $a(\cdot,v)$ *for fixed $v$ in some $V_m$*, and **density of $\bigcup V_n$** plus continuity extends the identity to all of $H_0^1$.

The unifying difficulty: this is existence proved **constructively** by finite-dimensional approximation, so one must track which facts are exact (the discrete equations), which are estimates (the bound), and which are limits (weak convergence + density).

## The Key Insight

The bilinear form is *exactly the $H^1$ inner product*:
$$
a(u,v):=(u,v)_{L^2}+(u',v')_{L^2}=\int_0^1\!\big(uv+u'v'\big)\,dx=\langle u,v\rangle_{H^1},\qquad a(u,u)=\|u\|_{H^1}^2 .
$$
So $a$ is automatically **bounded** ($|a(u,v)|\le\|u\|_{H^1}\|v\|_{H^1}$) and **coercive** ($a(u,u)=\|u\|_{H^1}^2$) with constant $1$ — no Poincaré needed. The functional $\ell(v)=(f,v)_{L^2}$ is bounded ($|\ell(v)|\le\|f\|_{L^2}\|v\|_{H^1}$). With this, every part is a short step:

- **(c)** coercivity $\Rightarrow$ uniqueness ($a(w,w)=0\Rightarrow w=0$); injective-on-finite-dimensional $\Rightarrow$ existence.
- **(d)** test against $u_n$: $\|u_n\|_{H^1}^2=a(u_n,u_n)=\ell(u_n)\le\|f\|_{L^2}\|u_n\|_{H^1}$, so $\|u_n\|_{H^1}\le\|f\|_{L^2}$; bounded $\Rightarrow$ weak subsequential limit in the Hilbert space $H_0^1$.
- **(e)** for $v\in V_m$ and $n\ge m$, $a(u_n,v)=\ell(v)$; weak convergence sends $a(u_n,v)\to a(u,v)$, so $a(u,v)=\ell(v)$ on $\bigcup V_m$, and **density + continuity** extends it to all of $H_0^1$.

The whole argument is "Lax–Milgram by hand," with the Hilbert structure of $a$ doing all the analytic work.

## Complete Proof

### Part (a): description of $H_0^1(0,1)$

$H^1(0,1)=\{u\in L^2(0,1):u'\in L^2(0,1)\}$, where $u'$ is the **distributional** derivative, with inner product $\langle u,v\rangle_{H^1}=\int_0^1(uv+u'v')\,dx$ and norm $\|u\|_{H^1}^2=\|u\|_{L^2}^2+\|u'\|_{L^2}^2$. In one dimension every $u\in H^1(0,1)$ has an **absolutely continuous representative** (the embedding $H^1(0,1)\hookrightarrow C([0,1])$), so pointwise values — in particular $u(0)$ and $u(1)$ — are well defined.

$H_0^1(0,1)$ is the **closure of $C_c^\infty(0,1)$ in the $H^1$-norm**. Equivalently,
$$
H_0^1(0,1)=\{u\in H^1(0,1):u(0)=u(1)=0\},
$$
the $H^1$-functions vanishing at both endpoints. It is a closed subspace of $H^1$, hence itself a **Hilbert space** under $\langle\cdot,\cdot\rangle_{H^1}$. (On $H_0^1$ the Poincaré inequality holds, so $\|u'\|_{L^2}$ is an equivalent norm — though we will not even need this, since $a$ is already the full $H^1$ inner product.)

### Part (b): equivalence of the weak and strong problems

Write $a(u,v)=\int_0^1(uv+u'v')\,dx$ and $\ell(v)=\int_0^1 fv\,dx$. The **weak problem** is: find $u\in H_0^1$ with $a(u,v)=\ell(v)$ for all $v\in H_0^1$.

**Strong $\Rightarrow$ weak.** Suppose $u\in H^2(0,1)\cap H_0^1(0,1)$ satisfies $u-u''=f$ a.e. and $u(0)=u(1)=0$. For any $v\in H_0^1$, multiply by $v$ and integrate:
$$
\int_0^1(u-u'')v\,dx=\int_0^1 fv\,dx .
$$
Integrate the $-u''v$ term by parts; the boundary term $[u'v]_0^1$ vanishes because $v(0)=v(1)=0$:
$$
-\int_0^1 u''v\,dx=\int_0^1 u'v'\,dx .
$$
Hence $\int_0^1(uv+u'v')\,dx=\int_0^1 fv\,dx$, i.e. $a(u,v)=\ell(v)$ for all $v\in H_0^1$: the weak problem holds.

**Weak $\Rightarrow$ strong.** Suppose $u\in H_0^1$ solves the weak problem. Test against $v\in C_c^\infty(0,1)\subset H_0^1$:
$$
\int_0^1 u'v'\,dx=\int_0^1(f-u)v\,dx .
$$
By the definition of the distributional derivative, $\int_0^1 u'v'\,dx=-\int_0^1 u''v\,dx$ (with $u''$ the distributional second derivative), so
$$
-\int_0^1 u''v\,dx=\int_0^1(f-u)v\,dx\qquad\text{for all }v\in C_c^\infty(0,1),
$$
which means $-u''=f-u$, i.e. $u-u''=f$ **in the sense of distributions**. Since $u\in L^2$ and $f\in L^2$, the identity $u''=u-f$ shows $u''\in L^2$, hence $u\in H^2(0,1)$; the equation then holds **a.e.** Finally $u\in H_0^1$ gives $u(0)=u(1)=0$. So $u$ solves the strong problem (with the natural regularity $u\in H^2\cap H_0^1$). The two problems are therefore equivalent. $\qquad\checkmark$

### Part (c): existence and uniqueness of the Galerkin approximant $u_n\in V_n$

The discrete problem is: find $u_n\in V_n$ with
$$
a(u_n,v)=\ell(v)\qquad\text{for all }v\in V_n. \tag{$D_n$}
$$
Let $d=\dim V_n$ and fix a basis $\phi_1,\dots,\phi_d$ of $V_n$. Writing $u_n=\sum_{j=1}^d c_j\phi_j$, $(D_n)$ is equivalent to the square linear system
$$
\sum_{j=1}^d a(\phi_j,\phi_i)\,c_j=\ell(\phi_i)\quad(i=1,\dots,d),\qquad\text{i.e. } A\mathbf c=\mathbf b,\ \ A_{ij}=a(\phi_j,\phi_i),\ \mathbf b_i=\ell(\phi_i).
$$

**Why uniqueness suffices (the hint).** $A$ is a square matrix, so the linear map $\mathbf c\mapsto A\mathbf c$ on the finite-dimensional space $\mathbb R^d$ is **injective if and only if surjective** (rank–nullity). Thus it is enough to prove uniqueness: uniqueness $=$ injectivity ($A\mathbf c=0\Rightarrow\mathbf c=0$) $\Rightarrow$ invertibility $\Rightarrow$ existence of a (unique) solution for the given right-hand side $\mathbf b$.

**Uniqueness via coercivity.** Suppose $u_n,\tilde u_n\in V_n$ both solve $(D_n)$. Then $w:=u_n-\tilde u_n\in V_n$ satisfies $a(w,v)=0$ for all $v\in V_n$. Choosing $v=w$,
$$
0=a(w,w)=\|w\|_{H^1}^2\ \Longrightarrow\ w=0 .
$$
So the solution is unique. By the finite-dimensional injective$\Rightarrow$surjective principle, $(D_n)$ has a **unique** solution $u_n\in V_n$. (Equivalently: $A_{ij}=\langle\phi_j,\phi_i\rangle_{H^1}$ is the Gram matrix of linearly independent vectors for an inner product, hence symmetric positive definite, hence invertible.) $\qquad\checkmark$

### Part (d): boundedness and the weak limit

Test $(D_n)$ against $v=u_n\in V_n$:
$$
\|u_n\|_{H^1}^2=a(u_n,u_n)=\ell(u_n)=(f,u_n)_{L^2}\le\|f\|_{L^2}\,\|u_n\|_{L^2}\le\|f\|_{L^2}\,\|u_n\|_{H^1},
$$
using Cauchy–Schwarz and $\|u_n\|_{L^2}\le\|u_n\|_{H^1}$. If $u_n\ne0$, divide by $\|u_n\|_{H^1}$ to get
$$
\boxed{\ \|u_n\|_{H^1}\le\|f\|_{L^2}\quad\text{for all }n\ }
$$
(and the bound is trivial if $u_n=0$). So $\{u_n\}$ is **bounded** in $H_0^1$, uniformly in $n$.

Now $H_0^1$ is a Hilbert space, hence reflexive, so **every bounded sequence has a weakly convergent subsequence** (Banach–Alaoglu together with reflexivity; equivalently, bounded sequences in a Hilbert space are weakly sequentially precompact). Therefore there is a subsequence $\{u_{n_k}\}$ and a $u\in H_0^1$ with
$$
u_{n_k}\rightharpoonup u\quad\text{weakly in }H_0^1(0,1).
$$
$\qquad\checkmark$

### Part (e): the weak limit solves the weak problem

Let $v\in\bigcup_{m\ge1}V_m$, say $v\in V_m$. For every index $n\ge m$ we have $V_m\subseteq V_n$, so $v\in V_n$ and $(D_n)$ gives
$$
a(u_n,v)=\ell(v)\qquad\text{for all }n\ge m. \tag{$\dagger$}
$$
For this fixed $v$, the map $w\mapsto a(w,v)=\langle w,v\rangle_{H^1}$ is a **bounded linear functional** on $H_0^1$. By definition of weak convergence, $u_{n_k}\rightharpoonup u$ implies $a(u_{n_k},v)\to a(u,v)$. Passing to the limit along the subsequence in $(\dagger)$ (valid once $n_k\ge m$),
$$
a(u,v)=\lim_{k\to\infty}a(u_{n_k},v)=\ell(v).
$$
Since $v\in V_m$ was arbitrary and $m$ was arbitrary, $a(u,v)=\ell(v)$ holds for **all** $v\in\bigcup_m V_m$.

Finally extend to all of $V=H_0^1$ by **density**. Both $v\mapsto a(u,v)$ and $v\mapsto\ell(v)$ are continuous (bounded) linear functionals on $H_0^1$: $|a(u,v)|\le\|u\|_{H^1}\|v\|_{H^1}$ and $|\ell(v)|\le\|f\|_{L^2}\|v\|_{H^1}$. They agree on the dense subspace $\bigcup_m V_m$, so they agree on its closure, which is all of $H_0^1$. Hence
$$
a(u,v)=\ell(v)\qquad\text{for all }v\in H_0^1(0,1),
$$
i.e. $u$ solves the weak problem of part (b). $\qquad\blacksquare$

### Remark — the full sequence converges, and what was really proved

This is the **Galerkin method**, and parts (c)–(e) together constitute a *constructive existence proof* for the weak (hence, by (b), the strong) boundary-value problem $u-u''=f$, $u(0)=u(1)=0$: solve in growing finite-dimensional subspaces, bound the approximants uniformly, and extract a weak limit that inherits the equation by density. Two closing points:

- **From subsequence to full sequence.** The weak problem has a *unique* solution (if $u,\tilde u$ both solve it, then $a(u-\tilde u,v)=0$ for all $v$; take $v=u-\tilde u$ to get $\|u-\tilde u\|_{H^1}=0$). Hence *every* weakly convergent subsequence of the bounded sequence $\{u_n\}$ has the same limit $u$, which forces the **entire** sequence $u_n\rightharpoonup u$.
- **The role of coercivity.** Because $a$ is the $H^1$ inner product, the abstract hypotheses of Lax–Milgram (boundedness + coercivity of $a$, boundedness of $\ell$) hold with the best possible constants, and the same testing-against-the-solution trick that bounds $u_n$ also yields the stability estimate $\|u\|_{H^1}\le\|f\|_{L^2}$ for the exact solution. In fact one can show $u_n\to u$ *strongly* (Céa's lemma gives $\|u-u_n\|_{H^1}=\min_{v\in V_n}\|u-v\|_{H^1}\to0$ by density), but the weak convergence proved here is already enough to identify the limit as the solution.

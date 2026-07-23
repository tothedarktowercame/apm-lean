<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m02A06: A semilinear boundary value problem by the contraction mapping principle

## Why It's Hard

The equation $-u_{xx}+u-\epsilon u^2=f$ is **nonlinear**, so there is no direct solution
formula. The standard move is to peel off the linear part $L=-\dfrac{d^2}{dx^2}+1$ (with
the given boundary data), which is invertible with a *contractive* inverse — $\|L^{-1}\|
\le1$ via the maximum principle — and to treat $\epsilon u^2$ as a perturbation, recasting
the BVP as a **fixed-point equation** $u=\Phi+\epsilon S[u^2]$. The difficulties are: (i)
absorbing the inhomogeneous boundary condition $u(0)=1$ into a base function so the
unknown lives in a space with zero boundary data; (ii) controlling the quadratic
nonlinearity, which is only *locally* Lipschitz — hence the contraction works on a bounded
ball and only for $\epsilon$ small.

## The Key Insight

Let $S[h]$ be the unique bounded solution of $-w_{xx}+w=h$, $w(0)=0$, $w(\infty)=0$; the
maximum principle gives $\|S[h]\|_\infty\le\|h\|_\infty$. Let $\Phi=e^{-x}+S[f]$ solve the
*linear* BVP $-\Phi_{xx}+\Phi=f$, $\Phi(0)=1$, $\Phi(\infty)=0$. Then
$$
u\ \text{solves the BVP}\iff u=\Phi+\epsilon\,S[u^2]=:T[u].
$$
Since $u^2-v^2=(u+v)(u-v)$, on the ball $\|u\|_\infty\le R$ the map $T$ is Lipschitz with
constant $\le 2\epsilon R$ and maps the ball into itself once $\epsilon$ is small; the
contraction mapping principle then yields a unique fixed point.

## Complete Proof

Work in the Banach space $X=C_0([0,\infty))$ of continuous functions vanishing at
$\infty$, with the sup norm $\|\cdot\|_\infty$ (complete).

### Step 1: the linear solution operator $S$ and the maximum-principle bound

For $h\in X$, the ODE $-w_{xx}+w=h$ with $w(0)=0$, $w(\infty)=0$ has a unique bounded
solution $w=S[h]$ (the homogeneous solutions are $e^{\pm x}$; decay at $\infty$ selects
$e^{-x}$, and the two boundary conditions determine $w$ uniquely via the Green's function
of $-\frac{d^2}{dx^2}+1$). It satisfies the **maximum-principle estimate**
$$
\|S[h]\|_\infty\le\|h\|_\infty .
$$
Indeed, if $w=S[h]$ attained a positive maximum at an interior point $x_0$, then
$w_{xx}(x_0)\le0$, so $w(x_0)=h(x_0)+w_{xx}(x_0)\le h(x_0)\le\|h\|_\infty$; at the
boundaries $w=0$. The symmetric argument bounds $-w$. Hence $\|w\|_\infty\le\|h\|_\infty$.
(Equivalently, $S=L^{-1}$ has $L^\infty\to L^\infty$ norm $\le1$.) Also $S[h]\in X$
(it $\to0$ at $\infty$).

### Step 2: absorb the boundary data into a base solution $\Phi$

The function $e^{-x}$ solves the homogeneous equation $-w_{xx}+w=0$ with $e^{-x}|_{x=0}=1$,
$e^{-x}\to0$. Set
$$
\Phi:=e^{-x}+S[f].
$$
Then $-\Phi_{xx}+\Phi=0+f=f$, $\Phi(0)=1+0=1$, $\Phi(\infty)=0$: $\Phi$ solves the linear
BVP. It is bounded, with
$$
\|\Phi\|_\infty\le 1+\|S[f]\|_\infty\le 1+\|f\|_\infty=:M_0
$$
($f$ is bounded, being smooth and compactly supported), and $\Phi\in X$.

### Step 3: the fixed-point reformulation

Suppose $u$ solves $-u_{xx}+u-\epsilon u^2=f$, $u(0)=1$, $u(\infty)=0$. Then $u-\Phi$
satisfies $-(u-\Phi)_{xx}+(u-\Phi)=\epsilon u^2$ with $(u-\Phi)(0)=0$, $(u-\Phi)(\infty)=0$,
so $u-\Phi=S[\epsilon u^2]=\epsilon S[u^2]$. Conversely, applying $-\frac{d^2}{dx^2}+1$ to
$u=\Phi+\epsilon S[u^2]$ recovers the equation and boundary conditions. Therefore
$$
u\ \text{solves the BVP}\quad\Longleftrightarrow\quad u=T[u],\qquad T[u]:=\Phi+\epsilon\,S[u^2].
$$

### Step 4: $T$ is a contraction self-map of a ball, for small $\epsilon$

Fix $R=2M_0$ and let $B=\{u\in X:\|u\|_\infty\le R\}$, a closed (hence complete) subset of
$X$.

**Self-map.** For $u\in B$, using Step 1 and $\|u^2\|_\infty=\|u\|_\infty^2\le R^2$,
$$
\|T[u]\|_\infty\le\|\Phi\|_\infty+\epsilon\|S[u^2]\|_\infty\le M_0+\epsilon R^2
=M_0+4\epsilon M_0^2 .
$$
This is $\le R=2M_0$ provided $4\epsilon M_0^2\le M_0$, i.e. $\epsilon\le\dfrac{1}{4M_0}$.

**Contraction.** For $u,v\in B$, since $u^2-v^2=(u+v)(u-v)$,
$$
\|T[u]-T[v]\|_\infty=\epsilon\|S[u^2-v^2]\|_\infty\le\epsilon\|(u+v)(u-v)\|_\infty
\le\epsilon\,\|u+v\|_\infty\|u-v\|_\infty\le 2\epsilon R\,\|u-v\|_\infty .
$$
With $R=2M_0$ this is $4\epsilon M_0\|u-v\|_\infty$, a contraction (constant $<1$) provided
$\epsilon<\dfrac{1}{4M_0}$.

So for
$$
0<\epsilon<\frac{1}{4M_0}=\frac{1}{4(1+\|f\|_\infty)},
$$
$T:B\to B$ is a contraction.

### Step 5: conclusion

By the contraction mapping principle (Banach fixed-point theorem) applied to $T$ on the
complete metric space $B$, there is a **unique** fixed point $u\in B$, and hence a unique
solution of the boundary value problem within $B$. Bootstrapping regularity: $u=\Phi+
\epsilon S[u^2]$ with $u$ continuous gives $u\in C^2$, and since $f$ is smooth, repeated
differentiation shows $u$ is smooth — a classical solution with $u(0)=1$, $u(\infty)=0$.
$\quad\blacksquare$

### Remark

This is the prototypical "invert the linear part, contract on the nonlinearity" argument.
The zeroth-order term $+u$ is what makes $L=-\partial_x^2+1$ satisfy the maximum principle
with $\|L^{-1}\|\le1$ (no Poincaré constant needed on the half-line), and the quadratic
nonlinearity is locally Lipschitz with constant $\sim2R$ on a ball of radius $R$, so the
smallness of $\epsilon$ buys the contraction. Uniqueness is *within* the ball $B$ (i.e.
among solutions of size $O(M_0)$); for small $\epsilon$ this is the physically relevant
branch bifurcating from the linear solution $\Phi$ at $\epsilon=0$. Larger $\epsilon$ can
in principle admit additional (large) solutions, which is why the contraction is local.

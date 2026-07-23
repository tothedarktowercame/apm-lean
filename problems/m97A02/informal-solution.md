<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m97A02: Local surjectivity of $\sin\circ x+x\circ\cos$ — an inverse function theorem on a $C^1$ space anchored at the Dottie number

Let $\alpha$ be the unique fixed point of cosine, $\cos\alpha=\alpha$ (the
**Dottie number**, $\alpha\approx0.739\in(0,1)$), and let
$$X=\{x\in C^1([0,1],\mathbb R):x(\alpha)=0\},\qquad \|x\|=\sup_{t\in[0,1]}|x'(t)|.$$
Define $\Phi:X\to X$ by
$$\Phi(x)(t)=\sin\big(x(t)\big)+x(\cos t).$$
We show: for $y\in X$ sufficiently close to $0$, there exists $x\in X$ with
$\Phi(x)=y$, i.e. $\sin\circ x+x\circ\cos=y$.

## Why It's Hard

- **The space is unusual and the norm only works because of $\alpha$.**
  $\|x\|=\sup|x'|$ is a *seminorm* on $C^1$ — it is a genuine norm only on the
  subspace where the one constant that escapes it is killed. The condition
  $x(\alpha)=0$ does exactly that: $\|x\|=0\Rightarrow x'\equiv0\Rightarrow x$
  constant $\Rightarrow x\equiv0$. One must first see that $(X,\|\cdot\|)$ is even
  a normed space, and then that it is **complete**.
- **The Dottie number is load-bearing, not decoration.** $\Phi$ must land back in
  $X$, i.e. $\Phi(x)(\alpha)=0$. This needs *both* $x(\alpha)=0$ *and*
  $\cos\alpha=\alpha$: $\Phi(x)(\alpha)=\sin(x(\alpha))+x(\cos\alpha)=\sin0+x(\alpha)=0$.
  Choose any other anchor point and $\Phi$ does not preserve the space.
- **Two different nonlinearities are entangled.** $\sin\circ x$ is an *outer*
  (Nemytskii / superposition) nonlinearity; $x\circ\cos$ is an *inner* linear
  composition (a weighted shift). They need different handling, and Fréchet
  differentiability of the superposition operator *in a derivative norm* is
  delicate — it works here only because the anchor gives a Poincaré bound
  $\|h\|_\infty\le\|h\|$.
- **Invertibility of the linearization is quantitative.** It comes down to
  $\|C\|\le\sin 1<1$, where the $<1$ is a lucky consequence of the domain being
  $[0,1]$ (so $\sup|\sin t|=\sin1$). On a longer interval this can fail.

## The Key Insight

This is the **inverse function theorem in Banach spaces**. The derivative of
$\Phi$ at $0$ is
$$D\Phi(0)h=h+h\circ\cos=(I+C)h,\qquad (Ch)(t)=h(\cos t),$$
and $C$ is a *contraction*: differentiating $h(\cos t)$ brings down a factor
$-\sin t$, and $\sup_{[0,1]}|\sin t|=\sin1\approx0.841<1$, so $\|C\|\le\sin1$ and
$I+C$ is invertible by Neumann series. The nonlinear part then collapses
beautifully — the inner-composition terms cancel:
$$\Phi(x)-D\Phi(0)x=\big(\sin\circ x+x\circ\cos\big)-\big(x+x\circ\cos\big)=\sin\circ x-x,$$
and $\sin u-u=O(u^3)$ is tiny near $0$. So $\Phi$ is a small nonlinear
perturbation of an invertible linear map: a local diffeomorphism at $0$, hence
locally onto.

## Complete Proof

### Step 0 — $(X,\|\cdot\|)$ is a Banach space

The map $J:X\to C([0,1])$, $Jx=x'$, is linear, isometric ($\|x\|=\|x'\|_\infty$),
and surjective: given $u\in C([0,1])$, the function $x(t)=\int_\alpha^t u(s)\,ds$
lies in $X$ (it is $C^1$, $x'=u$, $x(\alpha)=0$) with $Jx=u$. It is injective
because $x'=0$ and $x(\alpha)=0$ force $x\equiv0$. Thus $J$ is an isometric
isomorphism $X\cong C([0,1])$, and since $C([0,1])$ is complete, **$X$ is a Banach
space**. (Concretely, the Poincaré-type bound
$$|h(t)|=\Big|\int_\alpha^t h'\Big|\le|t-\alpha|\,\|h\|\le\|h\|\quad\Rightarrow\quad \|h\|_\infty\le\|h\|$$
holds for every $h\in X$, used repeatedly below.)

### Step 1 — $\Phi$ maps $X$ into $X$

For $x\in X$: $\Phi(x)=\sin\circ x+x\circ\cos$ is $C^1$ (compositions of $C^1$
maps; note $\cos:[0,1]\to[\cos1,1]\subseteq[0,1]$, so $x\circ\cos$ is defined).
At the anchor,
$$\Phi(x)(\alpha)=\sin\big(x(\alpha)\big)+x(\cos\alpha)=\sin0+x(\alpha)=0,$$
using $x(\alpha)=0$ and $\cos\alpha=\alpha$. Hence $\Phi(x)\in X$, and $\Phi(0)=0$.

### Step 2 — the linearization $L=I+C$ is invertible

Let $(Ch)(t)=h(\cos t)$. Then $Ch\in X$ (since $Ch(\alpha)=h(\cos\alpha)=h(\alpha)=0$),
and
$$(Ch)'(t)=-\sin t\,\cdot h'(\cos t)\ \Rightarrow\ \|Ch\|=\sup_t|\sin t|\,|h'(\cos t)|\le(\sin1)\,\|h\|,$$
because $\sup_{[0,1]}|\sin t|=\sin1$ and $\cos t\in[0,1]$. So $\|C\|\le\sin1<1$,
and by the Neumann series $L^{-1}=(I+C)^{-1}=\sum_{n\ge0}(-C)^n$ converges with
$$\|L^{-1}\|\le\frac{1}{1-\sin1}=:\kappa\ (\approx6.3).$$

### Step 3 — reformulate $\Phi(x)=y$ as a fixed point

Write $\Phi(x)=Lx+N(x)$ with the nonlinear remainder
$$N(x)=\Phi(x)-Lx=\big(\sin\circ x+x\circ\cos\big)-\big(x+x\circ\cos\big)=\sin\circ x-x,$$
i.e. $N(x)(t)=\sin(x(t))-x(t)$. (Note $N(x)\in X$: $N(x)(\alpha)=\sin0-0=0$.) The
equation $\Phi(x)=y$ is equivalent to
$$x=\Psi(x):=L^{-1}\big(y-N(x)\big).$$

**$N$ is Lipschitz with small constant on a small ball.** For $\|x_1\|,\|x_2\|\le r$,
differentiate $N(x_1)-N(x_2)=(\sin x_1-x_1)-(\sin x_2-x_2)$:
$$\frac{d}{dt}\big[\cdots\big]=(\cos x_1-1)(x_1'-x_2')+(\cos x_1-\cos x_2)\,x_2'.$$
Using $|\cos x_1-1|\le\tfrac12 x_1^2\le\tfrac12 r^2$ (and $\|x_1\|_\infty\le r$),
$|\cos x_1-\cos x_2|\le|x_1-x_2|\le\|x_1-x_2\|$, and $|x_2'|\le r$:
$$\|N(x_1)-N(x_2)\|\le\Big(r+\tfrac12 r^2\Big)\|x_1-x_2\|=:\lambda(r)\,\|x_1-x_2\|,\qquad \lambda(r)\xrightarrow{r\to0}0.$$
In particular $\|N(x)\|=\|N(x)-N(0)\|\le\lambda(r)\,r$ for $\|x\|\le r$.

### Step 4 — contraction and conclusion

Fix $r=r_0>0$ small enough that $\kappa\,\lambda(r_0)\le\tfrac12$, and set
$\delta:=\dfrac{r_0}{2\kappa}$. Let $\|y\|<\delta$ and work on the closed ball
$\overline B_{r_0}=\{x\in X:\|x\|\le r_0\}$ (a complete metric space).

- **Self-map.** For $\|x\|\le r_0$,
  $\|\Psi(x)\|\le\kappa\big(\|y\|+\|N(x)\|\big)\le\kappa\|y\|+\kappa\lambda(r_0)r_0
  \le\kappa\delta+\tfrac12 r_0=\tfrac12 r_0+\tfrac12 r_0=r_0.$
- **Contraction.** For $x_1,x_2\in\overline B_{r_0}$,
  $\|\Psi(x_1)-\Psi(x_2)\|=\|L^{-1}(N(x_2)-N(x_1))\|\le\kappa\lambda(r_0)\|x_1-x_2\|\le\tfrac12\|x_1-x_2\|.$

By the Banach fixed-point theorem, $\Psi$ has a (unique) fixed point
$x\in\overline B_{r_0}$, which solves
$$\boxed{\ \sin\circ x+x\circ\cos=y.\ }$$
Moreover $\|x\|\le\kappa\|y\|+\tfrac12\|x\|$ gives the size estimate
$\|x\|\le 2\kappa\|y\|$. Since $\delta$ depends only on the fixed data, this proves
local solvability for all $y\in X$ with $\|y\|<\delta$. $\blacksquare$

*(This is precisely the constructive proof of the surjective half of the inverse
function theorem: $\Phi$ is $C^1$ near $0$ with $D\Phi(0)=I+C$ a toplinear
isomorphism, hence a local $C^1$-diffeomorphism carrying a neighborhood of $0$
onto a neighborhood of $\Phi(0)=0$.)*

## What Connects

**To the inverse/implicit function theorem in Banach spaces.** The whole problem
is the IFT with the two hypotheses made explicit: completeness of $X$ and
invertibility of $D\Phi(0)$. The contraction in Step 4 is the standard proof of
the theorem's surjective half, with quantitative radius $r_0$ and threshold
$\delta$.

**To Nemytskii (superposition) operators.** The outer term $\sin\circ x$ is a
superposition operator; its Fréchet derivative is multiplication by $\cos\circ x$.
A recurring subtlety is that such operators are often *not* differentiable in
$C^k$ norms unless the nonlinearity is smooth — here $\sin$ is entire, and the
anchor's Poincaré bound $\|h\|_\infty\le\|h\|$ is what lets the derivative-norm
estimates close.

**To composition operators and the Dottie number.** The inner term $x\circ\cos$
is a composition (substitution) operator; its norm is governed by the derivative
of the inner map, here $-\sin t$ with $\sup_{[0,1]}|\sin t|=\sin1<1$. The fixed
point $\alpha=\cos\alpha$ is the natural anchor making the affine-shift structure
$I+C$ preserve $X$; it is the same Dottie number that arises as the global
attractor of iterating cosine.

**To Poincaré inequalities.** The bound $\|h\|_\infty\le\|h\|=\sup|h'|$ for
$h(\alpha)=0$ is a one-dimensional Poincaré inequality; it is exactly what makes
the derivative-only norm control the function itself, and is used in both the
linear estimate (Step 2) and the nonlinear estimate (Step 3).

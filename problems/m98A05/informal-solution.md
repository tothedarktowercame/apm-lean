<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98A05: The Implicit Function Theorem, parameter persistence, and a nonlinear Dirichlet problem via non-resonance

## Why It's Hard

This three-part problem walks from the abstract Implicit Function Theorem (IFT)
to a concrete semilinear boundary-value problem, and the difficulty escalates:

- **(a)** demands the *precise* Banach-space statement: the map must be $C^1$, and
  it is the **partial** derivative in the unknown — not the full derivative — that
  must be a *toplinear isomorphism* (bounded inverse), with the conclusion a
  *unique $C^1$ implicit function*.
- **(b)** hides a matching subtlety. The IFT requires
  $D_xH(x_0,\epsilon_0)=DF(x_0)+\epsilon_0\,DG(x_0)$ invertible, yet the
  hypothesis only gives "$DF(x_0)$ invertible." These agree exactly when
  $\epsilon_0=0$; for $\epsilon_0\neq0$ one must invoke that invertibility is an
  *open* condition.
- **(c)** is where the analysis lives. One must (i) choose function spaces so the
  problem becomes $H(w,\epsilon)=0$ between Banach spaces
  ($H^2\cap H^1_0\to L^2$), (ii) check the quadratic nonlinearity $w^2$ is $C^1$
  — which works only through the **Sobolev embedding** $H^2\hookrightarrow C^0$ —
  and (iii) verify the linearization $w\mapsto w''-w$ is invertible. Step (iii) is
  a disguised **non-resonance** condition: it holds because $1$ is *not* a
  Dirichlet eigenvalue of $-d^2/dx^2$. The sign of the "$+w$" term is chosen
  precisely to dodge the eigenvalue that a "$-w$" would hit.

## The Key Insight

**Parameter persistence is just the IFT with the parameter as one of the
variables**, and the *only* thing to check is invertibility of the linearization
at the base solution. For the BVP, the base solution is $w\equiv0$ at
$\epsilon=0$, and the linearization $F=\dfrac{d^2}{dx^2}-1$ is invertible because
the Dirichlet spectrum of $-\dfrac{d^2}{dx^2}$ on $(0,\pi)$ is $\{n^2:n\ge1\}$,
which **misses** $1$ — equivalently $-\dfrac{d^2}{dx^2}+1$ is positive definite,
so $w''-w=f$ is uniquely solvable. The nonlinearity $w^2$ is harmless: $H^2(0,\pi)$
embeds into $C^0[0,\pi]$, so squaring is a smooth map into $L^2$. Everything
reduces to "linearization invertible $\Rightarrow$ solution persists."

## Complete Proof

### Part (a) — Statement of the Implicit Function Theorem

**Theorem (IFT, Banach spaces).** Let $X,P,Z$ be Banach spaces, $U\subseteq X\times
P$ open, and $H\in C^1(U,Z)$. Suppose $(x_0,p_0)\in U$ satisfies
$$H(x_0,p_0)=0,$$
and that the partial Fréchet derivative
$$D_xH(x_0,p_0)\in\mathcal L(X,Z)\quad\text{is a toplinear isomorphism (bounded, bijective, with bounded inverse).}$$
Then there exist open neighborhoods $W\ni x_0$ in $X$ and $V\ni p_0$ in $P$, and a
unique map $\varphi\in C^1(V,W)$ with $\varphi(p_0)=x_0$, such that for
$(x,p)\in W\times V$,
$$H(x,p)=0\iff x=\varphi(p).$$
Moreover $D\varphi(p_0)=-\big[D_xH(x_0,p_0)\big]^{-1}D_pH(x_0,p_0)$.

### Part (b) — Persistence of solutions under perturbation

Let $X,Y$ be Banach spaces, $F,G\in C^1(X,Y)$, and
$$H:X\times\mathbb R\to Y,\qquad H(x,\epsilon)=F(x)+\epsilon\,G(x).$$

**$H$ is $C^1$.** $F$ is $C^1$ by hypothesis; $(x,\epsilon)\mapsto\epsilon G(x)$ is
$C^1$ as a product of the $C^1$ map $G$ with the smooth scalar $\epsilon$ (its
derivative at $(x,\epsilon)$ sends $(h,\sigma)\mapsto \epsilon\,DG(x)h+\sigma\,G(x)$).
Hence $H\in C^1(X\times\mathbb R,Y)$, with partial derivative in $x$
$$D_xH(x,\epsilon)=DF(x)+\epsilon\,DG(x).$$

**Invertibility of $D_xH$ at the base point.** We are given $H(x_0,\epsilon_0)=0$
and $DF(x_0)$ invertible. Take the parameter to be $\epsilon$ and the unknown to be
$x$.

- *If $\epsilon_0=0$* (the standard case, and the one used in part (c)):
  $D_xH(x_0,0)=DF(x_0)$ is invertible by hypothesis.
- *For $\epsilon_0\neq0$ small:* the set of invertible operators is open in
  $\mathcal L(X,Y)$, and $\|D_xH(x_0,\epsilon_0)-DF(x_0)\|=|\epsilon_0|\,\|DG(x_0)\|$.
  By the Neumann-series criterion, $D_xH(x_0,\epsilon_0)$ is invertible whenever
  $|\epsilon_0|<\dfrac{1}{\|DF(x_0)^{-1}\|\,\|DG(x_0)\|}$.

In either case $D_xH(x_0,\epsilon_0)$ is a toplinear isomorphism.

**Apply the IFT.** With $H(x_0,\epsilon_0)=0$ and $D_xH(x_0,\epsilon_0)$
invertible, the IFT yields a neighborhood of $\epsilon_0$ and a unique $C^1$ map
$\epsilon\mapsto x(\epsilon)$ with $x(\epsilon_0)=x_0$ and
$$H\big(x(\epsilon),\epsilon\big)=F\big(x(\epsilon)\big)+\epsilon\,G\big(x(\epsilon)\big)=0$$
for all $\epsilon$ sufficiently close to $\epsilon_0$. $\blacksquare$

### Part (c) — A solution of $w''=w+\epsilon w^2$, $\ w(0)=w(\pi)=0$, for small $\epsilon$

**Function-space setup.** Let
$$X=H^2(0,\pi)\cap H^1_0(0,\pi)\quad(\text{the }H^2\text{ functions with }w(0)=w(\pi)=0),\qquad Y=L^2(0,\pi).$$
Both are Banach (Hilbert) spaces; the Dirichlet conditions make sense pointwise
because $H^2(0,\pi)\hookrightarrow C^1[0,\pi]$. The problem
$w''-w-\epsilon w^2=0$ is $H(w,\epsilon)=0$ with
$$F(w)=w''-w,\qquad G(w)=-w^2,\qquad H(w,\epsilon)=F(w)+\epsilon\,G(w).$$

**$F\in C^1(X,Y)$.** $F$ is bounded linear ($\|w''-w\|_{L^2}\le\|w\|_{H^2}+\|w\|_{L^2}\le 2\|w\|_{H^2}$),
hence $C^\infty$ with $DF(w)=F$.

**$G\in C^1(X,Y)$.** By the Sobolev embedding $X\hookrightarrow C^0[0,\pi]$, every
$w\in X$ is continuous and bounded, so $w^2\in C^0\subseteq L^2$ and
$\|w^2\|_{L^2}\le\sqrt\pi\,\|w\|_{C^0}^2\le C\|w\|_X^2$. The quadratic map
$w\mapsto -w^2$ is then $C^1$ (indeed smooth) from $X$ to $Y$, with
$DG(w)h=-2wh$ (and $\|2wh\|_{L^2}\le 2\|w\|_{C^0}\|h\|_{C^0}\sqrt\pi\le C\|w\|_X\|h\|_X$).

**Base solution.** At $\epsilon=0$ the equation is $w''-w=0$, $w(0)=w(\pi)=0$. The
general solution of $w''=w$ is $w=Ae^{x}+Be^{-x}$; the boundary conditions give
$A+B=0$ and $Ae^\pi+Be^{-\pi}=0$, forcing $A=B=0$. So $w_0\equiv0$ is the unique
solution, and $H(0,0)=0$: take $(w_0,\epsilon_0)=(0,0)$.

**The linearization $D_wH(0,0)=F$ is invertible — the crux.** We must show that for
every $f\in L^2(0,\pi)$ the problem
$$w''-w=f,\qquad w(0)=w(\pi)=0$$
has a unique solution $w\in X$ depending boundedly on $f$. Write it as
$-w''+w=-f$. The bilinear form on $H^1_0(0,\pi)$,
$$a(w,v)=\int_0^\pi\big(w'v'+wv\big)\,dx,$$
is bounded and **coercive**: $a(w,w)=\|w'\|_{L^2}^2+\|w\|_{L^2}^2=\|w\|_{H^1}^2$.
By Lax–Milgram there is a unique weak solution $w\in H^1_0$ with $\|w\|_{H^1}\le
\|f\|_{L^2}$. Elliptic regularity (or directly: $w''=w-f\in L^2$) gives $w\in H^2$,
so $w\in X$, and
$$\|w\|_{H^2}\le C\big(\|w''\|_{L^2}+\|w\|_{L^2}\big)\le C\big(\|w-f\|_{L^2}+\|w\|_{L^2}\big)\le C'\|f\|_{L^2}.$$
Thus $F:X\to Y$ is a bounded linear bijection with bounded inverse: **invertible.**

*Why this works — non-resonance.* The Dirichlet eigenvalues of $-d^2/dx^2$ on
$(0,\pi)$ are $\{n^2:n=1,2,\dots\}$ with eigenfunctions $\sin(nx)$. Invertibility
of $F=d^2/dx^2-1$ is exactly the statement that $1\notin\{n^2\}$ — equivalently
$-d^2/dx^2+1$ has spectrum $\{n^2+1\}\subseteq[2,\infty)$, bounded away from $0$.
The "$+w$" on the right-hand side is what places the shift at $+1$ (away from the
spectrum); a "$-w$" would give $d^2/dx^2+1$, which *annihilates* $\sin x$
($1=1^2$ is an eigenvalue) — a resonance that breaks the IFT and would require
Lyapunov–Schmidt instead.

**Conclude via (b).** $H\in C^1(X\times\mathbb R,Y)$, $H(0,0)=0$, and
$D_wH(0,0)=F$ is invertible. By part (b) / the IFT there is a $C^1$ branch
$\epsilon\mapsto w(\epsilon)\in X$ with $w(0)=0$ and
$$w(\epsilon)''=w(\epsilon)+\epsilon\,w(\epsilon)^2,\qquad w(\epsilon)(0)=w(\epsilon)(\pi)=0,$$
for all sufficiently small $\epsilon$. In particular, for small $\epsilon$ there
exists a solution $w\in H^2(0,\pi)$. $\blacksquare$

**Honest remark.** Since $w\equiv0$ satisfies $w''=w+\epsilon w^2$ for *every*
$\epsilon$ (both sides vanish), bare existence is trivial. The substance of the
argument is twofold: it is the *systematic* method (which produces a solution even
when no obvious one exists, e.g. with a forcing term $w''=w+\epsilon w^2+g$), and
the IFT's uniqueness clause shows the branch through $(0,0)$ is **locally unique**
— for small $\epsilon$, $w\equiv0$ is the *only* solution in an $H^2$-neighborhood
of $0$, so no nontrivial small-amplitude solution bifurcates. That non-bifurcation
is again the non-resonance $1\notin\{n^2\}$ at work.

## What Connects

**To Lyapunov–Schmidt and bifurcation.** The IFT applies exactly when the
linearization is invertible (non-resonance). At a resonance — e.g. $w''=-w+\epsilon
w^2$, where $\ker=\mathrm{span}\{\sin x\}$ — the IFT fails and one splits off the
kernel (Lyapunov–Schmidt reduction), which is where genuine bifurcation of
nontrivial branches occurs. This problem is the "easy side" deliberately set away
from the bifurcation point.

**To the Fredholm alternative.** Invertibility of $d^2/dx^2-\lambda$ on the
Dirichlet space holds iff $\lambda\notin\{-n^2\}$; at the eigenvalues the
Fredholm alternative governs solvability of the linear problem and the structure
of the nonlinear one. Here $\lambda=1$ gives $-\lambda=-1\notin\{-n^2\}$:
unconditional solvability.

**To elliptic regularity and Sobolev embeddings.** Two standard analytic inputs do
the heavy lifting: $H^2\hookrightarrow C^0$ (making the quadratic nonlinearity a
$C^1$ Nemytskii map into $L^2$) and the elliptic estimate
$\|w\|_{H^2}\lesssim\|f\|_{L^2}$ (making the linearization a *bounded* isomorphism,
not just a bijection). These are the one-dimensional shadows of the general
machinery for semilinear elliptic PDE.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM aunk03: Evaluating ∑1/k⁴ = π⁴/90 by residue summation with π·cot(πz)

## Why It's Hard

The strategy is not something one stumbles into — it must be *recognized*: deliberately introduce the auxiliary function $\pi\cot(\pi z)$ as a **summation kernel** whose poles sit at every integer with residue exactly $1$, so that $\dfrac{\pi\cot(\pi z)}{z^4}$ has residue $1/n^4$ at each integer $n\ne0$ and thereby *encodes the target series in its residues*. Once that move is made, three separate pieces of real work remain, each a classic stumbling block:

1. **Two residue computations of opposite character.** The integer poles are simple and easy (they give the series), but the pole at the origin is of **order 5**, and extracting its residue forces you to know the Laurent expansion of $\cot$ to the $z^3$ term — i.e. the coefficient $-\pi^4/45$, secretly a Bernoulli number. Mishandling this single coefficient is the most common way the problem goes wrong.

2. **The analytic crux: the contour integral must vanish.** This is not a hand-wave — it needs a *uniform* bound $|\cot(\pi z)|\le\coth(\pi/2)$ valid on **every** square in the family, independent of $N$. The half-integer corners $(n+\tfrac12)(1\pm i)$ are chosen for exactly this reason: they keep the contour a fixed distance from all the poles, where $\cot$ stays bounded.

3. **Assembling the pieces.** One must combine the residue theorem ("integral $=2\pi i\sum$ residues") with the vanishing of the integral to conclude that the *total* residue sum is $0$, then solve that single scalar equation for the series.

## The Key Insight

$\pi\cot(\pi z)$ has a **simple pole with residue $1$ at every integer** (and nowhere else). Dividing by $z^4$ therefore plants a pole of residue $1/n^4$ at each nonzero integer $n$ — the function *is* the series, read off as residues. Integrating over the square $C_N$ of half-side $N+\tfrac12$ and letting $N\to\infty$:

- the $1/z^4$ decay against a contour of length $\sim 8N$ and a *bounded* $\cot$ forces $\oint_{C_N}\to 0$;
- so by the residue theorem the **sum of all residues is zero**:
$$
0=\underbrace{\operatorname{Res}_{z=0}f}_{\text{closed form}}+\underbrace{\sum_{n\ne 0}\frac{1}{n^4}}_{=\,2\sum_{k\ge1}1/k^4}.
$$

The residue at the origin is the $z^3$-coefficient of $\pi\cot(\pi z)$, namely $-\pi^4/45$, and solving gives $\sum_{k\ge1}1/k^4=\tfrac12\cdot\tfrac{\pi^4}{45}=\pi^4/90$. The whole evaluation is "all residues sum to zero, and one of them is the answer."

## Complete Proof

Let $f(z)=\dfrac{\pi\cot(\pi z)}{z^4}=\dfrac{\pi\cos(\pi z)}{z^4\sin(\pi z)}$, and let $C_N$ be the positively oriented square with corners $\pm(N+\tfrac12)(1\pm i)$ — i.e. $\{\,|\Re z|\le N+\tfrac12,\ |\Im z|\le N+\tfrac12\,\}$, with $N\in\mathbb{N}$.

### Step 1 — Poles and residues of $f$ at the integers

$\sin(\pi z)$ vanishes exactly at $z\in\mathbb{Z}$, simply, so $\pi\cot(\pi z)$ has simple poles there. At $z=n\in\mathbb{Z}$,
$$
\operatorname{Res}_{z=n}\pi\cot(\pi z)=\frac{\pi\cos(\pi n)}{\frac{d}{dz}\sin(\pi z)\big|_{z=n}}=\frac{\pi\cos(\pi n)}{\pi\cos(\pi n)}=1 .
$$
For $n\ne 0$ the factor $z^{-4}$ is holomorphic and nonzero at $z=n$, so
$$
\operatorname{Res}_{z=n}f=\frac{1}{n^4}\cdot 1=\frac{1}{n^4}\qquad(n\ne0). \tag{1}
$$
Pairing $\pm n$ gives $\operatorname{Res}_{z=n}f+\operatorname{Res}_{z=-n}f=\dfrac1{n^4}+\dfrac1{(-n)^4}=\dfrac{2}{n^4}$.

### Step 2 — Residue at the origin (order-5 pole)

Near $z=0$, expand $\cot$. With $w=\pi z$, the Taylor series $\cos w=1-\frac{w^2}{2}+\frac{w^4}{24}-\cdots$ and $\sin w=w\big(1-\frac{w^2}{6}+\frac{w^4}{120}-\cdots\big)$ give, by dividing the series,
$$
w\cot w=\frac{1-\frac{w^2}{2}+\frac{w^4}{24}-\cdots}{1-\frac{w^2}{6}+\frac{w^4}{120}-\cdots}=1-\frac{w^2}{3}-\frac{w^4}{45}-\cdots
$$
(the $w^4$ coefficient is $\tfrac{7}{360}-\tfrac1{12}+\tfrac1{24}=-\tfrac1{45}$). Hence $\cot w=\frac1w-\frac{w}{3}-\frac{w^3}{45}-\cdots$, and with $w=\pi z$,
$$
\pi\cot(\pi z)=\frac1z-\frac{\pi^2}{3}z-\frac{\pi^4}{45}z^3-\cdots .
$$
Dividing by $z^4$,
$$
f(z)=\frac{1}{z^5}-\frac{\pi^2}{3}\,\frac{1}{z^3}-\frac{\pi^4}{45}\,\frac{1}{z}-\cdots,
$$
so the residue (coefficient of $z^{-1}$) is
$$
\operatorname{Res}_{z=0}f=-\frac{\pi^4}{45}. \tag{2}
$$

### Step 3 — The contour integral tends to $0$

**Uniform bound on $\cot$.** Writing $z=x+iy$,
$$
|\cot(\pi z)|^2=\frac{\cos^2(\pi x)+\sinh^2(\pi y)}{\sin^2(\pi x)+\sinh^2(\pi y)} .
$$
*On the horizontal sides* $|y|=N+\tfrac12\ge\tfrac12$: dropping $\sin^2$ and bounding $\cos^2\le1$,
$$
|\cot(\pi z)|^2\le\frac{1+\sinh^2(\pi y)}{\sinh^2(\pi y)}=\coth^2(\pi y)\le\coth^2\!\big(\tfrac{\pi}{2}\big).
$$
*On the vertical sides* $x=\pm(N+\tfrac12)$: by $\pi$-periodicity $\cot(\pi z)=\cot\!\big(\tfrac\pi2+i\pi y\big)=-\tan(i\pi y)=-i\tanh(\pi y)$, so $|\cot(\pi z)|\le1\le\coth(\tfrac\pi2)$. Thus on **all** of $C_N$,
$$
|\pi\cot(\pi z)|\le M:=\pi\coth\!\big(\tfrac{\pi}{2}\big),
$$
a constant **independent of $N$**.

**ML-estimate.** Every point of $C_N$ satisfies $|z|\ge N+\tfrac12$ (nearest points are the side-midpoints), so $|z^{-4}|\le(N+\tfrac12)^{-4}$; the contour has length $8(N+\tfrac12)$. Therefore
$$
\left|\oint_{C_N}f(z)\,dz\right|\le M\cdot\frac{1}{(N+\frac12)^4}\cdot 8\big(N+\tfrac12\big)=\frac{8M}{(N+\frac12)^3}\xrightarrow[N\to\infty]{}0. \tag{3}
$$

### Step 4 — Residue theorem and solving for the series

The poles of $f$ inside $C_N$ are $z=0,\pm1,\dots,\pm N$. By the **Residue Theorem** and $(1)$–$(2)$,
$$
\frac{1}{2\pi i}\oint_{C_N}f(z)\,dz=\operatorname{Res}_{z=0}f+\sum_{n=1}^{N}\frac{2}{n^4}=-\frac{\pi^4}{45}+2\sum_{n=1}^{N}\frac{1}{n^4}.
$$
Letting $N\to\infty$, the left side $\to0$ by $(3)$, so
$$
0=-\frac{\pi^4}{45}+2\sum_{n=1}^{\infty}\frac{1}{n^4}\quad\Longrightarrow\quad \sum_{n=1}^{\infty}\frac{1}{n^4}=\frac{1}{2}\cdot\frac{\pi^4}{45}.
$$
$$
\boxed{\;\sum_{k=1}^{\infty}\frac{1}{k^4}=\frac{\pi^4}{90}.\;}\qquad\blacksquare
$$

### Remark — the general mechanism

The argument computes $\zeta(2m)$ for every $m\ge1$ verbatim: replace $z^4$ by $z^{2m}$, and $\sum 1/k^{2m}=-\tfrac12\operatorname{Res}_{z=0}\big[\pi\cot(\pi z)z^{-2m}\big]$, which is $-\tfrac12$ times the $z^{2m-1}$-coefficient of $\pi\cot(\pi z)$ — a rational multiple of $\pi^{2m}$ governed by the Bernoulli numbers ($\zeta(2)=\pi^2/6$, $\zeta(4)=\pi^4/90$, $\zeta(6)=\pi^6/945,\dots$). Two design choices make it work: $\pi\cot(\pi z)$ is the canonical kernel with **unit residues at all integers and no other poles**, and the **half-integer square** keeps $\cot$ uniformly bounded so the kernel's growth never spoils the $z^{-2m}$ decay. The odd powers fail precisely because the $\pm n$ residues then cancel ($1/n^{2m+1}+1/(-n)^{2m+1}=0$) rather than reinforce — which is the analytic reflection of the still-mysterious arithmetic of $\zeta(\text{odd})$.

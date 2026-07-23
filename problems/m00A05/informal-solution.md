<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m00A05: u' + u = cos(u) — global well-posedness by contraction, and convergence to the Dottie fixed point

## Why It's Hard

The equation $u'+u=\cos u$ hides a clean structure behind two different techniques
that the two parts demand. For (a) "use the contraction mapping theorem," the
naive Picard operator $\Phi u=u_0+\int_0^t(\cos u-u)$ works only on tiny
intervals; the slick move is to fold the linear term $+u$ into an **integrating
factor**, turning the ODE into $u(t)=u_0e^{-t}+\int_0^t e^{-(t-s)}\cos u(s)\,ds$,
whose kernel $e^{-(t-s)}$ has integral $1-e^{-t}<1$ — so on any finite $[0,T]$ the
operator is a genuine contraction with constant $1-e^{-T}$, and $\cos$ being
$1$-Lipschitz is exactly what makes the constant land below $1$. For (b), the trap
is to look for an explicit solution; instead notice the ODE is **autonomous**,
$u'=F(u)$ with $F(u)=\cos u-u$ strictly decreasing through a single zero $\xi$ (the
"Dottie number," $\xi=\cos\xi\approx0.739$). Then every trajectory is monotone,
trapped on one side of the equilibrium by uniqueness, and forced to $\xi$ —
*independent of $u_0$*, which is the striking part: a globally attracting fixed
point.

## The Key Insight

**(a)** Integrating factor $e^{t}$ gives $\frac{d}{dt}(e^{t}u)=e^{t}\cos u$, hence
the fixed-point equation
$$
u=\Phi u,\qquad (\Phi u)(t)=u_0e^{-t}+\int_0^t e^{-(t-s)}\cos\!\big(u(s)\big)\,ds .
$$
Since $|\cos a-\cos b|\le|a-b|$ and $\int_0^t e^{-(t-s)}ds=1-e^{-t}$,
$$
\|\Phi u-\Phi v\|_{C[0,T]}\le(1-e^{-T})\,\|u-v\|_{C[0,T]},\qquad 1-e^{-T}<1,
$$
so Banach's theorem yields a unique solution on each $[0,T]$, hence on
$[0,\infty)$.

**(b)** $F(u)=\cos u-u$ has $F'(u)=-\sin u-1\le0$ (strictly decreasing), with a
**unique** zero $\xi$ ($\cos\xi=\xi$); $F>0$ left of $\xi$, $F<0$ right of $\xi$.
By uniqueness no trajectory crosses the constant solution $\xi$, so each $u$ is
monotone and bounded toward $\xi$, forcing $u(t)\to\xi$ for every $u_0$.

## Complete Proof

### Part (a): existence and uniqueness via contraction mapping

**Reformulation as an integral equation.** Multiply $u'+u=\cos u$ by the
integrating factor $e^{t}$: $\frac{d}{dt}\big(e^{t}u(t)\big)=e^{t}\cos(u(t))$.
Integrating from $0$ to $t$ and using $u(0)=u_0$,
$$
u(t)=u_0e^{-t}+\int_0^t e^{-(t-s)}\cos\!\big(u(s)\big)\,ds=:(\Phi u)(t).\tag{1}
$$
A continuous $u$ solving (1) is automatically $C^1$ (the right side is
differentiable, its integrand being continuous), and differentiating (1) returns
$u'(t)=\cos(u(t))-u(t)$ with $u(0)=u_0$; conversely any $C^1$ solution of the IVP
satisfies (1). So the IVP on $[0,T]$ is **equivalent** to the fixed-point equation
$u=\Phi u$ in $C([0,T])$.

**$\Phi$ is a contraction on $C([0,T])$.** Equip $X=C([0,T])$ with the sup norm; it
is complete, and $\Phi$ maps $X\to X$ (the right side of (1) is continuous in $t$).
For $u,v\in X$, using $|\cos a-\cos b|\le|a-b|$ (mean value theorem,
$|\sin|\le1$),
$$
|(\Phi u)(t)-(\Phi v)(t)|
\le\int_0^t e^{-(t-s)}\,\big|\cos u(s)-\cos v(s)\big|\,ds
\le\int_0^t e^{-(t-s)}\,|u(s)-v(s)|\,ds .
$$
Bounding $|u(s)-v(s)|\le\|u-v\|_{\infty}$ and computing
$\int_0^t e^{-(t-s)}ds=1-e^{-t}\le1-e^{-T}$ for $t\le T$,
$$
\|\Phi u-\Phi v\|_{\infty}\le\big(1-e^{-T}\big)\,\|u-v\|_{\infty},
\qquad k:=1-e^{-T}<1 .
$$
By the **contraction mapping theorem**, $\Phi$ has a unique fixed point
$u\in C([0,T])$ — the unique solution of the IVP on $[0,T]$.

**Globalization.** The constant $k=1-e^{-T}<1$ is available for every finite $T$,
so we obtain a unique solution on each $[0,T]$. By uniqueness these solutions agree
on overlaps (the restriction of the $[0,T_2]$-solution to $[0,T_1]$ is a fixed
point of $\Phi$ on $C([0,T_1])$, hence equals the $[0,T_1]$-solution). Patching
them gives a unique solution $u$ on all of $[0,\infty)$ for each $u_0\in\mathbb{R}$.
$\quad\checkmark$

### Part (b): all solutions converge to $\xi$, where $\xi=\cos\xi$

The equation is **autonomous**: $u'(t)=F(u(t))$ with $F(u)=\cos u-u$.

**$F$ is strictly decreasing with a unique zero $\xi$.** $F$ is $C^1$ with
$F'(u)=-\sin u-1\le0$, and $F'(u)=0$ only at the isolated points
$u=-\tfrac{\pi}{2}+2k\pi$. Hence for $u_1<u_2$,
$F(u_2)-F(u_1)=\int_{u_1}^{u_2}(-\sin u-1)\,du<0$, so $F$ is **strictly
decreasing**. Since $F$ is continuous with $F(0)=1>0$ and $F(\pi/2)=-\pi/2<0$,
there is a **unique** $\xi\in(0,\pi/2)$ with
$$
F(\xi)=0,\quad\text{i.e.}\quad \cos\xi=\xi
$$
(the "Dottie number," $\xi\approx0.739085$). Strict monotonicity gives the sign
pattern
$$
F(u)>0\ \text{ for }u<\xi,\qquad F(u)<0\ \text{ for }u>\xi.\tag{2}
$$
The constant function $u\equiv\xi$ solves the ODE.

**No trajectory meets the equilibrium.** Fix a solution $u$ with $u(0)=u_0$. If
$u(t_1)=\xi$ for some $t_1\ge0$, then $u$ and the constant solution $\xi$ agree at
$t_1$; by the uniqueness from part (a) (the IVP has a unique solution forward and
the equation is time-translation invariant), $u\equiv\xi$. So unless $u_0=\xi$, we
have $u(t)\neq\xi$ for all $t$, and by continuity $u(t)$ keeps the sign of
$u_0-\xi$:
$$
u_0>\xi\Rightarrow u(t)>\xi\ \forall t,\qquad
u_0<\xi\Rightarrow u(t)<\xi\ \forall t.
$$

**Monotonic convergence.** Suppose $u_0>\xi$ (the case $u_0<\xi$ is symmetric;
$u_0=\xi$ gives $u\equiv\xi$). Then $u(t)>\xi$ for all $t$, so by (2)
$u'(t)=F(u(t))<0$: $u$ is **strictly decreasing** and bounded below by $\xi$.
Therefore $u(t)\downarrow\ell$ for some $\ell\ge\xi$. If $\ell>\xi$, then
$u(t)\ge\ell>\xi$ for all $t$ and, $F$ being decreasing, $u'(t)=F(u(t))\le
F(\ell)<0$; integrating, $u(t)\le u(0)+F(\ell)\,t\to-\infty$, contradicting
$u(t)\ge\ell$. Hence $\ell=\xi$, i.e.
$$
\lim_{t\to\infty}u(t)=\xi .
$$
Symmetrically, if $u_0<\xi$ then $u$ is strictly increasing, bounded above by
$\xi$, and converges up to $\xi$. In every case
$$
\boxed{\ \lim_{t\to\infty}u(t)=\xi,\qquad \xi=\cos\xi,\ }
$$
**independent of $u_0$**. $\quad\blacksquare$

### Remark

Part (a)'s trick — absorbing the linear term into an integrating factor — is what
makes the contraction *global in time on each finite interval* with the explicit
constant $1-e^{-T}$; without it, $\cos u-u$ is still globally Lipschitz (constant
$2$) so Picard would also give global existence, but the integrating-factor form
hands you the contraction for free and exposes the equilibrium. Part (b) is the
phase line: a scalar autonomous ODE whose vector field $F$ is strictly decreasing
through a single root has that root as a **globally asymptotically stable**
equilibrium — every orbit slides monotonically into $\xi$. A one-line energy
version of the same fact: with $v=u-\xi$, $\frac{d}{dt}\tfrac12 v^2=vF(\xi+v)<0$
whenever $v\neq0$ (since $F$ decreases through its zero at $\xi$), so $v^2$ strictly
decreases to $0$. The constant $\xi$ is exactly the fixed point of $\cos$, tying
the long-time behavior back to the contraction theme of part (a).

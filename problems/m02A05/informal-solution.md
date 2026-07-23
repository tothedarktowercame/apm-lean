<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02A05: A coupled variational problem — decouple, then a Poincaré check decides min vs max

## Why It's Hard

This is a full calculus-of-variations problem on a **coupled** functional: the cross term $2xy$ links the two unknowns, so the Euler–Lagrange equations form a *system* ($x''=y$, $y''=x$) rather than two independent ODEs. Solving it (a 4th-order problem, $x''''=x$) and applying four boundary conditions is the routine part. The genuinely hard part is (c)–(d): deciding whether the unique extremal is a global minimum, a maximum, or neither. A critical point of a variational problem need not be an extremum, and here the term $+2xy$ (equivalently $-v^2$ after diagonalizing) threatens to make the functional indefinite. Resolving this requires the **second variation** and a sharp **Poincaré / Jacobi conjugate-point** estimate: the sign of $\int[(v')^2-v^2]$ on the interval hinges on whether the first Dirichlet eigenvalue exceeds $1$. The interval length $\pi/2$ is chosen right at the edge of the danger zone, and missing the eigenvalue comparison is the way to get the answer wrong.

## The Key Insight

The cross term $2xy$ is **diagonalized by $u=x+y$, $v=x-y$**, which turns the coupled EL system into two scalar equations:
$$
u''=u\quad(\text{hyperbolic, harmless}),\qquad v''=-v\quad(\text{oscillatory, all the subtlety}).
$$
The functional itself splits cleanly:
$$
J=\tfrac12\int_0^{\pi/2}\!\big[(u')^2+u^2\big]\,dt+\tfrac12\int_0^{\pi/2}\!\big[(v')^2-v^2\big]\,dt .
$$
The first integral is positive-definite; the second is governed by the Dirichlet eigenvalues $\lambda_n=4n^2$ on $[0,\pi/2]$. Because the smallest, $\lambda_1=4$, **exceeds the coefficient $1$ of $-v^2$**, the Poincaré inequality $\int(v')^2\ge 4\int v^2$ forces $\int[(v')^2-v^2]\ge 3\int v^2\ge 0$. So $J$ is strictly convex and coercive: the unique extremal is the **global minimum**, and high-frequency oscillations make $J$ unbounded above, so there is **no maximum**.

## Complete Proof

The Lagrangian is $L=(x')^2+(y')^2+2xy$, with $x(0)=y(0)=0$, $x(\pi/2)=y(\pi/2)=1$.

### Part (a): Euler–Lagrange equations

$\dfrac{d}{dt}L_{x'}-L_x=0$ gives $\dfrac{d}{dt}(2x')-2y=0$, and similarly for $y$:
$$
\boxed{x''=y,\qquad y''=x.}
$$

### Part (b): all extremals

Diagonalize with $u=x+y$, $v=x-y$. Adding/subtracting the EL equations,
$$
u''=x''+y''=y+x=u,\qquad v''=x''-y''=y-x=-v.
$$
The boundary conditions become $u(0)=0,\ u(\pi/2)=2$ and $v(0)=0,\ v(\pi/2)=0$.

- $u''=u$: general solution $u=a\cosh t+b\sinh t$. From $u(0)=0$, $a=0$; from $u(\pi/2)=2$, $b=\dfrac{2}{\sinh(\pi/2)}$. So $u(t)=\dfrac{2\sinh t}{\sinh(\pi/2)}$.
- $v''=-v$: general solution $v=c\cos t+d\sin t$. From $v(0)=0$, $c=0$; from $v(\pi/2)=0$, $d\sin(\pi/2)=d=0$. So $v\equiv 0$.

Hence $x=\tfrac12(u+v)=\tfrac12 u$ and $y=\tfrac12(u-v)=\tfrac12 u$ coincide:
$$
\boxed{x(t)=y(t)=\frac{\sinh t}{\sinh(\pi/2)},}
$$
the **unique** extremal. (Equivalently, $x''''=x$ gives $x=Ae^t+Be^{-t}+C\cos t+D\sin t$ with $y=x''$; the four boundary conditions force $C=D=0$, $B=-A$, $A=\tfrac{1}{2\sinh(\pi/2)}$, and $y=x$.)

*Note on uniqueness:* the only place a second extremal could enter is the $v$-equation; $v=d\sin t$ vanishes at both endpoints only if $\sin(\pi/2)=0$, which is false. The interval $[0,\pi/2]$ avoids the conjugate point.

### Part (c): the global minimum exists

Substitute $x=\tfrac12(u+v),\ y=\tfrac12(u-v)$ into $J$. Using $(x')^2+(y')^2=\tfrac12[(u')^2+(v')^2]$ and $2xy=\tfrac12(u^2-v^2)$,
$$
J=\tfrac12\underbrace{\int_0^{\pi/2}\!\big[(u')^2+u^2\big]dt}_{=:J_u[u]}+\tfrac12\underbrace{\int_0^{\pi/2}\!\big[(v')^2-v^2\big]dt}_{=:J_v[v]},
$$
with $u(0)=0,u(\pi/2)=2$ and $v(0)=v(\pi/2)=0$. Both pieces are quadratic, and **both are convex and coercive**:

- $J_u[u]=\int[(u')^2+u^2]\ge 0$ is manifestly a positive-definite quadratic form; its second variation $\int[(\eta')^2+\eta^2]>0$ for any nonzero variation $\eta$ (vanishing at the endpoints).
- $J_v[v]=\int[(v')^2-v^2]$: the Dirichlet eigenvalue problem $-v''=\lambda v$, $v(0)=v(\pi/2)=0$ has eigenvalues $\lambda_n=(n\pi/(\pi/2))^2=4n^2$ ($n\ge1$), so by the variational (Poincaré) inequality $\int_0^{\pi/2}(v')^2\,dt\ge\lambda_1\int_0^{\pi/2}v^2\,dt=4\int_0^{\pi/2}v^2\,dt$. Hence
$$
J_v[v]=\int(v')^2-\int v^2\ \ge\ 4\int v^2-\int v^2=3\int v^2\ \ge 0,
$$
with equality iff $v\equiv 0$. (Coercivity: $J_v[v]\ge\tfrac34\int(v')^2$ likewise.)

Therefore $J=\tfrac12 J_u+\tfrac12 J_v$ is a **strictly convex, coercive** functional on the admissible affine space, so it attains a unique global minimum at its unique critical point — the extremal of part (b):
$$
\boxed{\text{global minimum attained at }x(t)=y(t)=\frac{\sinh t}{\sinh(\pi/2)}.}
$$
Equivalently, the second variation $\delta^2 J=\int[(p')^2+p^2]+\int[(q')^2-q^2]\ (p=\eta+\xi,\ q=\eta-\xi)$ is positive for all nonzero admissible variations, the Jacobi/conjugate-point condition holding since $\lambda_1=4>1$. $\qquad\checkmark$

### Part (d): no global maximum

$J$ is **unbounded above**, so no maximum exists. Consider the admissible family (same boundary values as the minimizer, since $\sin(2nt)$ vanishes at $t=0$ and $t=\pi/2$, where $\sin(n\pi)=0$):
$$
x_n(t)=y_n(t)=\frac{\sinh t}{\sinh(\pi/2)}+\sin(2nt),\qquad n=1,2,\dots
$$
Since $x_n=y_n$, $J[x_n,y_n]=\int_0^{\pi/2}\big[2(x_n')^2+2x_n^2\big]\,dt$. The term $x_n'=x_*'+2n\cos(2nt)$ contributes
$$
\int_0^{\pi/2}2(x_n')^2\,dt\ \ge\ \int_0^{\pi/2}2\big(2n\cos(2nt)\big)^2\,dt-\text{(lower order)}=8n^2\cdot\frac{\pi}{4}-O(n)=2\pi n^2-O(n)\to\infty,
$$
while the remaining terms grow at most linearly in $n$. Hence $J[x_n,y_n]\to+\infty$, so $J$ has no global maximum. $\qquad\blacksquare$

### Remark — the conjugate point governs everything

The whole problem turns on diagonalizing the cross term: $u=x+y$ rides the *stable* (hyperbolic) mode $u''=u$, contributing only positive energy, while $v=x-y$ rides the *oscillatory* mode $v''=-v$, where the indefinite term $-v^2$ lives. Positivity of the second variation — hence existence of the minimum and uniqueness of the extremal — is precisely the **Jacobi condition**: no conjugate point in $(0,\pi/2]$, equivalently the first Dirichlet eigenvalue $\lambda_1=4$ exceeding the threshold $1$. The interval length is the knob: on $[0,L]$ the $v$-mode has $\lambda_1=(\pi/L)^2$, and positivity needs $(\pi/L)^2>1$, i.e. $L<\pi$. At $L=\pi$ the conjugate point appears ($v=\sin t$ solves $v''=-v$ with $v(0)=v(\pi)=0$), the second variation degenerates, extremals are non-unique, and the minimum can fail to exist — the classic boundary between "minimizer" and "saddle" in the calculus of variations. The absence of a maximum (d) is generic for such quadratic functionals: the gradient-squared term $\int(x')^2$ is unbounded above under admissible high-frequency perturbations.

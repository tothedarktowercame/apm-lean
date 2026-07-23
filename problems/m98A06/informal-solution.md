<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98A06: Extrema of $\int_0^a(y'^2-y^2)\,dx$ — conjugate points at multiples of $\pi$, and the Poincaré constant

## Why It's Hard

All three parts share the **same Euler–Lagrange equation** $y''+y=0$, yet they have completely different answers — and the reason is the single most important phenomenon in the second-variation theory of the calculus of variations: **conjugate points**. For this functional the conjugate points sit exactly at the multiples of $\pi$, and the length $a$ relative to $\pi$ decides everything:

- **(a) $a=2\pi$ (a multiple of $\pi$).** The boundary-value problem for $y''+y=0$ is at **resonance**: $\sin a=0$, so the boundary conditions either over- or under-determine the constants. Here they under-determine, giving **infinitely many extremals** — and the second variation is *indefinite*, so none is a genuine minimum or maximum.
- **(b) $a$ not a multiple of $\pi$.** Now $\sin a\ne0$, the BVP is **uniquely solvable**, and there is exactly one extremal. But whether it *minimizes* still depends on whether $a<\pi$ (before the first conjugate point) or $a>\pi$ (after it) — the trap is to call the unique extremal a minimum without checking.
- **(c) $a=\pi$ with an isoperimetric constraint.** The constraint converts the problem into an **eigenvalue problem** $-y''=\lambda y$, and the smallest eigenvalue is precisely the reciprocal of the **best Poincaré constant**. The subtlety is recognizing that "minimize $\int(y'^2-y^2)$ on the constraint sphere" *is* the variational characterization of $\lambda_1$.

The difficulty is not the EL equation — it is reading off, in each regime, how $a$ versus $\pi$ controls existence, uniqueness, and the sign of the second variation.

## The Key Insight

For $I(y)=\int_0^a(y'^2-y^2)\,dx$ the integrand is $L=y'^2-y^2$, so $L_y=-2y$, $L_{y'}=2y'$, and the **Euler–Lagrange equation** is
$$
\frac{d}{dx}(2y')-(-2y)=0\ \Longrightarrow\ y''+y=0\ \Longrightarrow\ y(x)=A\cos x+B\sin x .
$$
Everything else is the **second variation**: for an admissible variation $\eta$ (vanishing where $y$ is fixed),
$$
I(y+\eta)-I(y)=\underbrace{2\!\int_0^a(y'\eta'-y\eta)\,dx}_{=0\text{ by EL + BC}}+\underbrace{\int_0^a(\eta'^2-\eta^2)\,dx}_{Q(\eta)} ,
$$
so the extremal is a minimum iff $Q(\eta)=\int_0^a(\eta'^2-\eta^2)\ge0$ for all such $\eta$. By the Dirichlet eigenvalues $(\pi/a)^2,(2\pi/a)^2,\dots$ of $-\eta''$ on $[0,a]$, the smallest is $(\pi/a)^2$, and
$$
Q\ge0\ \iff\ \Big(\tfrac{\pi}{a}\Big)^2\ge1\ \iff\ a\le\pi .
$$
That single inequality — *is $a$ within the first conjugate point $\pi$?* — runs all three parts:

- **(a)** $a=2\pi>\pi$: $Q$ is indefinite, and $\sin(2\pi)=0$ gives a one-parameter family of extremals, all with $I=0$, none extremal.
- **(b)** unique extremal $y=\sin x/\sin a$; it is a **minimum** iff $a<\pi$, a saddle if $a>\pi$.
- **(c)** $a=\pi$ is the borderline; the constrained minimum gives first eigenvalue $\lambda_1=1$ and **best Poincaré constant $C=1/\lambda_1=1$**.

## Complete Proof

The extremals of $I$ solve $y''+y=0$, i.e. $y(x)=A\cos x+B\sin x$, as derived above. We treat the three cases. The second-variation form $Q(\eta)=\int_0^a(\eta'^2-\eta^2)\,dx$ over $\eta$ with $\eta=0$ at the fixed endpoints will decide the nature of each extremal; recall the Dirichlet eigenpairs on $[0,a]$: $-\phi_n''=\big(\tfrac{n\pi}{a}\big)^2\phi_n$, $\phi_n(x)=\sin\tfrac{n\pi x}{a}$, and the **Wirtinger inequality** $\int_0^a\eta'^2\ge(\tfrac{\pi}{a})^2\int_0^a\eta^2$ with equality only for $\eta\propto\sin\tfrac{\pi x}{a}$.

### Part (a): $a=2\pi$, $y(0)=y(2\pi)=1$

Impose the boundary conditions on $y=A\cos x+B\sin x$:
$$
y(0)=A=1,\qquad y(2\pi)=A\cos2\pi+B\sin2\pi=A=1 .
$$
The second condition is satisfied **automatically** (it reduces to $A=1$), leaving $B$ free. Hence there is a **one-parameter family of extremals**
$$
y_B(x)=\cos x+B\sin x,\qquad B\in\mathbb{R} .
$$
Their common value of $I$: with $y_B'=-\sin x+B\cos x$,
$$
y_B'^2-y_B^2=-\cos2x-2B\sin2x+B^2\cos2x,
$$
and since $\int_0^{2\pi}\cos2x\,dx=\int_0^{2\pi}\sin2x\,dx=0$, we get $I(y_B)=0$ for every $B$.

**None is a genuine extremum.** The second variation $Q(\eta)=\int_0^{2\pi}(\eta'^2-\eta^2)$ (over $\eta$ with $\eta(0)=\eta(2\pi)=0$) is **indefinite**: taking the first mode $\eta_1=\sin\tfrac{x}{2}$ (so $\eta_1(0)=\eta_1(2\pi)=0$),
$$
Q(\eta_1)=\int_0^{2\pi}\Big(\tfrac14\cos^2\tfrac x2-\sin^2\tfrac x2\Big)dx=\tfrac14\cdot\pi-\pi=-\tfrac{3\pi}{4}<0,
$$
while higher modes $\eta_n=\sin\tfrac{nx}{2}$ with $n\ge3$ give $Q(\eta_n)=\big((\tfrac n2)^2-1\big)\cdot\pi>0$. So along the family $y_B$ the functional has directions of decrease *and* increase: the extremals are **saddle points**, and $I$ has **no minimum or maximum** under these data. (This is the resonance/degeneracy caused by $a=2\pi$ lying beyond the first conjugate point $\pi$.) $\qquad\checkmark$

### Part (b): $a$ not a multiple of $\pi$, $y(0)=0$, $y(a)=1$

Impose the conditions on $y=A\cos x+B\sin x$:
$$
y(0)=A=0,\qquad y(a)=B\sin a=1 .
$$
Since $a$ is **not** a multiple of $\pi$, $\sin a\ne0$, so $B=1/\sin a$ is determined: there is a **unique extremal**
$$
\boxed{\,y(x)=\frac{\sin x}{\sin a}\,}.
$$
Its energy: with $y'=\cos x/\sin a$, $y'^2-y^2=\cos2x/\sin^2a$, and $\int_0^a\cos2x\,dx=\tfrac12\sin2a=\sin a\cos a$, so
$$
I(y)=\frac{\sin a\cos a}{\sin^2a}=\cot a .
$$

**Nature of the extremal.** The second variation $Q(\eta)=\int_0^a(\eta'^2-\eta^2)$ over $\eta(0)=\eta(a)=0$ has smallest "eigenvalue gap" governed by Wirtinger:
$$
Q(\eta)\ge\Big(\big(\tfrac{\pi}{a}\big)^2-1\Big)\int_0^a\eta^2 .
$$
- If $0<a<\pi$: $(\pi/a)^2>1$, so $Q(\eta)>0$ for all $\eta\ne0$. Because $I$ is quadratic, $I(y+\eta)-I(y)=Q(\eta)>0$, so $y=\sin x/\sin a$ is the **strict (global) minimizer**, with minimum value $\cot a$.
- If $a>\pi$ (and not a multiple of $\pi$): $(\pi/a)^2<1$, and the first mode $\eta_1=\sin\tfrac{\pi x}{a}$ gives $Q(\eta_1)=\big((\tfrac\pi a)^2-1\big)\cdot\tfrac a2<0$, while high modes give $Q>0$. So $Q$ is indefinite and the unique extremal is a **saddle** — $I$ has no extremum.

Thus there is always exactly one extremal $y=\sin x/\sin a$; it is a genuine minimum precisely when $a<\pi$ (i.e. before the first conjugate point). $\qquad\checkmark$

### Part (c): $a=\pi$, $y(0)=y(\pi)=0$, constraint $\int_0^\pi y^2\,dx=1$; the Poincaré constant

This is an **isoperimetric (constrained) variational problem**. Introduce a Lagrange multiplier $\mu$ and extremize $J(y)=\int_0^\pi(y'^2-y^2)\,dx-\mu\big(\int_0^\pi y^2\,dx-1\big)$. The integrand $y'^2-(1+\mu)y^2$ has Euler–Lagrange equation
$$
y''+(1+\mu)y=0,\qquad y(0)=y(\pi)=0 .
$$
This is the **Dirichlet eigenvalue problem** $-y''=\lambda y$ on $[0,\pi]$ with $\lambda=1+\mu$. Its solutions are
$$
\lambda_n=n^2,\qquad y_n(x)=c_n\sin(nx),\quad n=1,2,3,\dots
$$
Normalizing by the constraint, $\int_0^\pi c_n^2\sin^2(nx)\,dx=c_n^2\cdot\tfrac\pi2=1$ gives $c_n=\sqrt{2/\pi}$. So the constrained **extremals** are
$$
y_n(x)=\sqrt{\tfrac2\pi}\,\sin(nx),\qquad n=1,2,3,\dots,
$$
and their energies are
$$
I(y_n)=\int_0^\pi(y_n'^2-y_n^2)\,dx=\lambda_n\!\int_0^\pi y_n^2-\int_0^\pi y_n^2=(\lambda_n-1)\cdot1=n^2-1 .
$$
Hence $I(y_n)=n^2-1$: the **minimum** is $I(y_1)=0$, attained at $y_1=\sqrt{2/\pi}\,\sin x$; there is no maximum since $I(y_n)=n^2-1\to\infty$.

**Best Poincaré constant.** The inequality $\int_0^\pi f^2\,dx\le C\int_0^\pi f'^2\,dx$ for $f\in H_0^1(0,\pi)$ holds with the **smallest** admissible $C$ equal to $1/\lambda_1$, where
$$
\lambda_1=\min_{0\ne f\in H_0^1}\frac{\int_0^\pi f'^2}{\int_0^\pi f^2}
$$
is exactly the first Dirichlet eigenvalue. From the computation above $\lambda_1=1$ (minimizer $f=\sin x$), so
$$
\int_0^\pi f^2\,dx\le \int_0^\pi f'^2\,dx,\qquad\boxed{\,C_{\text{best}}=\frac{1}{\lambda_1}=1\,},
$$
with **equality iff $f$ is a multiple of $\sin x$**. Equivalently, the statement $I(y)\ge0$ on the constraint set $\int y^2=1$ (with minimum $0$ at $y_1$) is *precisely* the Poincaré/Wirtinger inequality $\int f'^2\ge\int f^2$ with sharp constant $1$. $\qquad\blacksquare$

### Remark — conjugate points unify the three parts

The functional $\int_0^a(y'^2-y^2)$ is the textbook example where the **Jacobi conjugate-point condition** is visible by hand. The extremal field solves $y''+y=0$, whose solutions vanish at spacing $\pi$; the first conjugate point to $x=0$ is therefore $x=\pi$. The Jacobi criterion says an extremal minimizes only if the interval $[0,a]$ contains **no interior conjugate point**, i.e. $a\le\pi$:

- **(a)** $a=2\pi$ contains the conjugate point $\pi$ in its interior — minimization fails, and the resonance $\sin a=0$ also destroys uniqueness (a whole family of extremals).
- **(b)** $a<\pi$ gives a bona fide minimum $\cot a$; $a>\pi$ passes a conjugate point and the extremal becomes a saddle.
- **(c)** $a=\pi$ is the **critical length**: the second variation is positive semidefinite with a one-dimensional null space spanned by $\sin x$, and that borderline degeneracy is exactly the sharp Poincaré inequality with constant $1$ and extremal $\sin x$.

So a single number — the first Dirichlet eigenvalue $\lambda_1(a)=(\pi/a)^2$ compared to $1$ — controls existence, uniqueness, the sign of the second variation, and the optimal Poincaré constant.

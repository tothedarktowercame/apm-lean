<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99A01: Extremals of $\int_0^{\pi/2}\!\big[(y')^2+y^2+2y\big]\,dt$ — an inhomogeneous Euler–Lagrange equation and its unique minimizer

Find all extremals of
$$J[y]=\int_0^{\pi/2}\Big[(y'(t))^2+(y(t))^2+2y(t)\Big]\,dt\ \longrightarrow\ \text{extremum},\qquad y(0)=y(\tfrac{\pi}{2})=0.$$

## Why It's Hard

The mechanics are standard, but three things must be handled correctly to give a
*complete* answer:

- **The linear term makes Euler–Lagrange inhomogeneous.** The $2y$ in the
  integrand contributes a constant to the Euler–Lagrange equation, turning it into
  $y''-y=1$ rather than the homogeneous $y''-y=0$. One must find a particular
  solution, not just the hyperbolic homogeneous part — a common slip.
- **"Find all extremals" demands a uniqueness argument.** It is not enough to
  exhibit one solution; one must show the two boundary conditions pin down the
  constants uniquely (the associated homogeneous Dirichlet problem has only the
  trivial solution), so there is exactly one extremal.
- **The boundary constant wants simplification — and is a global minimizer.** The
  constant fixed by the right endpoint simplifies, via a hyperbolic half-angle
  identity, to the clean $\tanh(\pi/4)$. And because the integrand is convex in
  $(y,y')$, the single extremal is in fact the global minimizer, which is the
  honest answer to "extremum."

## The Key Insight

**Complete the square:** $y^2+2y=(y+1)^2-1$, so with $u:=y+1$,
$$J[y]=\int_0^{\pi/2}\big[(u')^2+u^2\big]\,dt-\tfrac{\pi}{2},\qquad u(0)=u(\tfrac{\pi}{2})=1.$$
This strips the problem down to the canonical Dirichlet energy
$\int(u'^2+u^2)$, whose Euler–Lagrange equation is $u''=u$, solved by hyperbolic
functions. The shift by the constant $-\tfrac{\pi}{2}$ does not affect extremals.
Convexity of $(u')^2+u^2$ (equivalently of the original integrand
$(y')^2+(y+1)^2-1$) guarantees that the unique critical point is the global
minimizer.

## Complete Proof

### Step 1 — The Euler–Lagrange equation

With $F(t,y,y')=(y')^2+y^2+2y$,
$$F_y=2y+2,\qquad F_{y'}=2y',\qquad \frac{d}{dt}F_{y'}=2y''.$$
The Euler–Lagrange equation $F_y-\dfrac{d}{dt}F_{y'}=0$ reads
$$2y+2-2y''=0\quad\Longleftrightarrow\quad \boxed{\,y''-y=1\,.}$$

### Step 2 — General solution of $y''-y=1$

The homogeneous equation $y''-y=0$ has solutions $\cosh t,\ \sinh t$. A particular
solution of $y''-y=1$ is the constant $y_p=-1$ (then $y_p''-y_p=0-(-1)=1$).
Hence
$$y(t)=A\cosh t+B\sinh t-1,\qquad A,B\in\mathbb R.$$
(Equivalently $y=A_1e^{t}+A_2e^{-t}-1$.)

### Step 3 — Impose the boundary conditions

- $y(0)=A\cosh 0+B\sinh 0-1=A-1=0\ \Rightarrow\ A=1.$
- $y(\tfrac{\pi}{2})=\cosh\tfrac{\pi}{2}+B\sinh\tfrac{\pi}{2}-1=0\ \Rightarrow\
  B=\dfrac{1-\cosh\frac{\pi}{2}}{\sinh\frac{\pi}{2}}.$

Simplify $B$ using the half-angle identities $\cosh u-1=2\sinh^2\!\tfrac{u}{2}$ and
$\sinh u=2\sinh\tfrac{u}{2}\cosh\tfrac{u}{2}$:
$$\frac{\cosh u-1}{\sinh u}=\frac{2\sinh^2\frac{u}{2}}{2\sinh\frac{u}{2}\cosh\frac{u}{2}}=\tanh\frac{u}{2}
\quad\Longrightarrow\quad B=-\tanh\!\Big(\frac{\pi}{4}\Big).$$

Therefore the extremal is
$$\boxed{\;y(t)=\cosh t-\tanh\!\Big(\tfrac{\pi}{4}\Big)\sinh t-1\;}$$
(numerically $\tanh(\pi/4)\approx0.6558$).

### Step 4 — Uniqueness: this is the *only* extremal

Any extremal solves the same linear ODE $y''-y=1$, so it has the form in Step 2;
the two boundary conditions form a linear system for $(A,B)$ whose homogeneous
version is
$$A\cosh 0+B\sinh 0=0,\qquad A\cosh\tfrac{\pi}{2}+B\sinh\tfrac{\pi}{2}=0,$$
i.e. $A=0$ and then $B\sinh\tfrac{\pi}{2}=0\Rightarrow B=0$ (since
$\sinh\tfrac{\pi}{2}\neq0$). The coefficient matrix is invertible, so $(A,B)$ is
uniquely determined. Equivalently, the homogeneous Dirichlet problem
$y''-y=0,\ y(0)=y(\tfrac{\pi}{2})=0$ has only $y\equiv0$, because $-1$ is not a
Dirichlet eigenvalue of $d^2/dt^2$ on $(0,\tfrac{\pi}{2})$. Hence the extremal is
unique.

### Step 5 — The extremal is the global minimizer

Rewrite the integrand by completing the square:
$$F=(y')^2+y^2+2y=(y')^2+(y+1)^2-1.$$
As a function of $(y,y')$ this is a sum of the convex maps $(y')^2$ and
$(y+1)^2$, minus a constant; its Hessian $\mathrm{diag}(2,2)$ is positive
definite, so $F$ is *strictly convex* in $(y,y')$. Consequently $J$ is strictly
convex on the affine space of admissible functions, the Euler–Lagrange equation
is both necessary and sufficient, and the unique extremal of Step 3 is the
**unique global minimizer** of $J$. (There is no maximizer: along
$y_n(t)=n\sin(2t)$, which respects the boundary conditions,
$J[y_n]\to+\infty$, so $J$ is unbounded above.) $\blacksquare$

## What Connects

**To completing the square / shifting the unknown.** The substitution $u=y+1$
turning $\int(y'^2+y^2+2y)$ into $\int(u'^2+u^2)$ minus a constant is the
variational analogue of absorbing a linear term into a quadratic form by a shift.
The linear term $2y$ only translates the minimizer; it never changes the
second-order (convexity) structure that decides whether an extremal minimizes.

**To Sturm–Liouville / non-resonance.** Solvability and uniqueness here are
governed by whether $-1$ lies in the Dirichlet spectrum of $d^2/dt^2$ on
$(0,\tfrac{\pi}{2})$ (eigenvalues $-(2n)^2$ for the interval of length
$\tfrac{\pi}{2}$, i.e. $-4,-16,\dots$). Since $-1$ avoids it, the boundary-value
problem is uniquely solvable — the same Fredholm/non-resonance mechanism that
makes inhomogeneous linear BVPs well-posed.

**To the second variation and convex calculus of variations.** The strict
convexity of $F$ in $(y,y')$ is exactly the strengthened Legendre condition
($F_{y'y'}=2>0$) together with $F_{yy}=2>0$, which makes the second variation
$\delta^2J=\int 2(\eta'^2+\eta^2)\,dt>0$ for every nonzero admissible variation
$\eta$. This is the clean case where a single critical point is automatically the
global minimizer — no field theory or conjugate-point analysis needed.

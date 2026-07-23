<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02J04: Euler–Lagrange, the Beltrami first integral, and the catenoid as the minimal surface of revolution

## Why It's Hard

This is a three-part problem that escalates from a definition to a genuine
nonlinear boundary-value problem, and each part feeds the next:

- **(a)** is the routine statement of the Euler–Lagrange equation — but you must
  get the total-derivative bookkeeping exactly right, because (b) and (c) lean on it.
- **(b)** asks for the **Beltrami identity**. The trap is the total derivative
  $\frac{d}{dx}F$: it expands as $F_y y' + F_{y'} y''$ *only because* $F$ has no
  **explicit** $x$-dependence (the $F_x$ term is absent). Miss that and the
  cancellation that drives the whole identity never happens.
- **(c)** is a concrete minimal-surface-of-revolution problem. You must (i)
  recognize that the area integrand $F = y\sqrt{1+y'^2}$ is $x$-free so the
  Beltrami identity applies, (ii) survive the algebra that collapses
  $F - y'F_{y'}$ to the strikingly simple $y/\sqrt{1+y'^2}$, (iii) separate and
  integrate the resulting first-order ODE — recognizing the integral as
  $\cosh^{-1}$ — and (iv) fit two boundary conditions to pin down the two
  constants. The pleasant surprise is that the endpoints
  $(0,1)$ and $(1,\cosh 1)$ are engineered so that the constants come out
  trivially: $C=1$, $D=0$, and the extremal is simply $y=\cosh x$.

## The Key Insight

**When $F$ does not depend explicitly on $x$, the second-order Euler–Lagrange
equation has a first integral** (the Beltrami identity)
$$F - y'F_{y'} = \text{const}.$$
This is the variational analogue of energy conservation for a time-independent
Lagrangian, and it turns a second-order ODE into a first-order one. For the
surface-area functional the first integral simplifies to
$$\frac{y}{\sqrt{1+y'^2}} = C,$$
whose solution is the **catenary** $y = C\cosh\!\big(\tfrac{x}{C}+D\big)$. The
surface it sweeps out is the **catenoid**, the only nonplanar minimal surface of
revolution.

## Complete Proof

### Part (a) — The Euler–Lagrange equation

For the functional $\Phi(y)=\int_a^b F(x,y(x),y'(x))\,dx$ with fixed endpoints,
a smooth extremal $y$ satisfies
$$\boxed{\;\frac{\partial F}{\partial y} - \frac{d}{dx}\!\left(\frac{\partial F}{\partial y'}\right) = 0\;}
\qquad\text{i.e.}\qquad F_y - \frac{d}{dx}F_{y'} = 0.$$

*Derivation (for completeness).* Let $\eta$ be any smooth variation with
$\eta(a)=\eta(b)=0$, and set $g(\varepsilon)=\Phi(y+\varepsilon\eta)$. A
stationary $y$ requires $g'(0)=0$:
$$g'(0)=\int_a^b\big(F_y\,\eta + F_{y'}\,\eta'\big)\,dx
= \int_a^b\Big(F_y - \frac{d}{dx}F_{y'}\Big)\eta\,dx,$$
after integrating the second term by parts and using $\eta(a)=\eta(b)=0$ to kill
the boundary term. Since this vanishes for **all** admissible $\eta$, the
fundamental lemma of the calculus of variations forces the bracket to vanish
pointwise, giving the Euler–Lagrange equation.

### Part (b) — The Beltrami identity when $F=F(y,y')$

Assume $F$ has no explicit $x$-dependence, $F=F(y,y')$. Differentiate the
quantity $F - y'F_{y'}$ along a curve $y(x)$:
$$\frac{d}{dx}\big(F - y'F_{y'}\big)
= \frac{dF}{dx} - y''F_{y'} - y'\frac{d}{dx}F_{y'}.$$

Because $F$ depends on $x$ only through $y$ and $y'$ (the explicit partial
$F_x$ is zero), the chain rule gives
$$\frac{dF}{dx} = F_y\,y' + F_{y'}\,y''.$$

Substitute:
$$\frac{d}{dx}\big(F - y'F_{y'}\big)
= \big(F_y\,y' + F_{y'}\,y''\big) - y''F_{y'} - y'\frac{d}{dx}F_{y'}
= y'\Big(F_y - \frac{d}{dx}F_{y'}\Big).$$

The $F_{y'}y''$ terms cancel, and the remaining factor in parentheses is exactly
the left-hand side of the Euler–Lagrange equation from part (a), which vanishes
on any extremal. Hence
$$\boxed{\;\frac{d}{dx}\big(F - y'F_{y'}\big) = 0\;}$$
along extremals, so $F - y'F_{y'}$ is constant. $\blacksquare$

### Part (c) — The minimal surface of revolution

We minimize the surface area
$$A = 2\pi\int_0^1 y\sqrt{1+y'^2}\,dx$$
over curves joining $(0,1)$ to $(1,\cosh 1)$. The integrand
$F(y,y') = y\sqrt{1+y'^2}$ has **no explicit $x$-dependence**, so by part (b) the
Beltrami first integral applies:
$$F - y'F_{y'} = C.$$

**Compute the first integral.** With $F = y\sqrt{1+y'^2}$,
$$F_{y'} = \frac{y\,y'}{\sqrt{1+y'^2}},
\qquad
y'F_{y'} = \frac{y\,y'^2}{\sqrt{1+y'^2}}.$$
Therefore
$$F - y'F_{y'}
= y\sqrt{1+y'^2} - \frac{y\,y'^2}{\sqrt{1+y'^2}}
= \frac{y\,(1+y'^2) - y\,y'^2}{\sqrt{1+y'^2}}
= \frac{y}{\sqrt{1+y'^2}}.$$
So the first integral is the remarkably clean
$$\frac{y}{\sqrt{1+y'^2}} = C. \tag{$\ast$}$$

**Solve the ODE.** Rearranging $(\ast)$:
$$y = C\sqrt{1+y'^2}\ \Longrightarrow\ y^2 = C^2(1+y'^2)
\ \Longrightarrow\ y' = \frac{\sqrt{y^2-C^2}}{C}.$$
Separate variables and integrate:
$$\int \frac{dy}{\sqrt{y^2-C^2}} = \int \frac{dx}{C}.$$
Using the hinted antiderivative
$\displaystyle\int \frac{dy}{\sqrt{y^2-C^2}} = \cosh^{-1}\!\Big(\frac{y}{C}\Big)
= \ln\!\big(y+\sqrt{y^2-C^2}\big)$, this gives
$$\cosh^{-1}\!\Big(\frac{y}{C}\Big) = \frac{x}{C} + D,$$
and inverting,
$$\boxed{\,y(x) = C\cosh\!\Big(\frac{x}{C} + D\Big)\,}$$
— the **catenary** with constants $C$ and $D$ to be fixed by the endpoints.

**Apply the boundary conditions.**
$$y(0) = C\cosh(D) = 1, \qquad y(1) = C\cosh\!\Big(\frac{1}{C}+D\Big) = \cosh 1.$$
Try $C = 1,\ D = 0$:
$$y(0) = \cosh(0) = 1\ \checkmark,\qquad
y(1) = \cosh(1)\ \checkmark.$$
Both conditions are satisfied, so the extremal is
$$\boxed{\,y(x) = \cosh x\,.}$$

**Conclusion.** The curve generating the minimum surface area when rotated about
the $x$-axis is the catenary $y = \cosh x$, and the surface it sweeps out is the
**catenoid**. This is consistent with the general principle that the only
nonplanar minimal surface of revolution is the catenoid. (The endpoints in this
problem are precisely the values of $\cosh x$ at $x=0$ and $x=1$, which is why
the constants collapse to $C=1$, $D=0$; for endpoint data spaced too far apart in
the $y$-direction relative to the $x$-gap, no catenary connects them and the
infimum is instead approached by the degenerate **Goldschmidt** two-disk
solution — but that pathology does not arise here.) $\blacksquare$

## What Connects

**To classical mechanics.** The Beltrami identity is the variational form of
energy conservation: when the Lagrangian $L(q,\dot q)$ has no explicit time
dependence, the Hamiltonian $H = \dot q\,L_{\dot q} - L$ is conserved. Part (b)
is exactly this statement with $x\leftrightarrow t$, $y\leftrightarrow q$.

**To minimal surfaces.** $(\ast)$ identifies the catenoid as a minimal surface
(zero mean curvature). The catenoid and the plane are the only minimal surfaces
of revolution — a theorem of Euler.

**To the existence subtlety (Goldschmidt solution).** Minimizers of the
surface-of-revolution problem do not always exist as smooth catenaries: when the
boundary radii are too large relative to their separation, the area infimum is
attained only in the limit by a degenerate surface consisting of two flat disks
joined by a line segment. This is a standard cautionary example that the
Euler–Lagrange equation gives *stationary* curves, and one must separately
confirm a genuine minimizer exists and is the catenary — which it is for the
data given here.

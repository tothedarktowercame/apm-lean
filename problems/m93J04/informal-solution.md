<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93J04: A Green's function for the Euler operator $x^2\partial_x^2-x\partial_x+1$ via its repeated indicial root

We are given the kernel on $(0,1)\times(0,1)$
$$\omega(x,y)=\begin{cases}\dfrac{x\ln y}{y^2}, & 0<x\le y<1,\\[2mm]\dfrac{x\ln x}{y^2}, & 0<y\le x<1,\end{cases}$$
and must show that, as a distribution, $\omega$ is a **fundamental solution**
(Green's function) of
$$L=x^2\frac{d^2}{dx^2}-x\frac{d}{dx}+\mathrm{id},\qquad Lu=x^2u''-xu'+u,$$
i.e. that for each fixed $y\in(0,1)$, $L_x\,\omega(\cdot,y)=\delta(x-y)$ in
$\mathcal D'(0,1)$.

## Why It's Hard

- **Where does the logarithm come from?** The kernel mixes $\ln y$ and $\ln x$ in
  the two branches, which looks arbitrary until one recognizes $L$ as an **Euler
  (equidimensional) operator** whose indicial equation has a *repeated* root.
  Repeated roots force the second homogeneous solution to carry a logarithm
  ($x\ln x$), and that is the only reason $\ln$ appears at all.
- **The leading coefficient is variable and degenerate.** $L$ is *not* in
  self-adjoint form, and its top coefficient $x^2$ both varies with $x$ and
  vanishes at the endpoint $x=0$. The jump condition that manufactures the delta
  must account for this: the identity $x^2\,\delta(x-y)=y^2\,\delta(x-y)$ is what
  converts the derivative jump into a *correctly normalized* delta.
- **Distribution vs. classical derivative.** $\omega(\cdot,y)$ has a corner at
  $x=y$. The delta is produced entirely by the jump in the first derivative
  through the formula $G''=\{G''\}+[G']_y\,\delta_y$; one must separate the
  (vanishing) classical part from the singular part.
- **The asymmetry $\ln y$ vs. $\ln x$ is structural, not a typo.** The
  logarithm always attaches to the *larger* of the two arguments. Seeing why is
  the whole game: the left branch must be the solution **regular at the singular
  endpoint $x=0$** (namely $\propto x$), the right branch is the other solution
  ($\propto x\ln x$), and continuity + the unit jump then pin the $y$-dependence.

## The Key Insight

$L$ is the Euler operator with indicial polynomial $(r-1)^2$: substituting
$u=x^r$ gives $Lu=(r-1)^2x^r$, a **double root** $r=1$. Hence the two homogeneous
solutions are
$$u_L(x)=x\quad(\text{regular at }x=0),\qquad u_R(x)=x\ln x.$$
The given $\omega$ is *exactly* the classical Green's function
$$G(x,y)=\frac{u_L(x_<)\,u_R(x_>)}{p_2(y)\,W(y)},\qquad x_<=\min(x,y),\ x_>=\max(x,y),$$
with $p_2(x)=x^2$ the leading coefficient and $W=u_Lu_R'-u_Ru_L'$ the Wronskian.
The logarithm rides on $x_>$ because $u_R=x\ln x$ is evaluated at the larger
argument — which is precisely the $\ln y$/$\ln x$ split in the problem. Verifying
"$\omega$ is a fundamental solution" reduces to three checkable facts:
**(1)** each branch is annihilated by $L$, **(2)** $\omega$ is continuous across
$x=y$, **(3)** the derivative jump equals $1/p_2(y)=1/y^2$, producing exactly
$+\delta(x-y)$.

## Complete Proof

### Step 0 — $L$ is Euler; the homogeneous solutions are $x$ and $x\ln x$

For $u=x^r$,
$$Lu=x^2\,r(r-1)x^{r-2}-x\,r x^{r-1}+x^r=\big(r(r-1)-r+1\big)x^r=(r-1)^2x^r.$$
The indicial equation $(r-1)^2=0$ has the double root $r=1$. The standard
reduction-of-order recipe for a repeated root gives the second solution
$x\ln x$. Direct check of both:
$$L(x)=x^2\cdot 0-x\cdot 1+x=0,$$
$$L(x\ln x)=x^2\!\left(\tfrac1x\right)-x(\ln x+1)+x\ln x=x-x\ln x-x+x\ln x=0,$$
using $(x\ln x)'=\ln x+1$, $(x\ln x)''=1/x$. So $u_L=x$ and $u_R=x\ln x$ span the
homogeneous solution space.

### Step 1 — each branch of $\omega$ solves $L_x\,\omega=0$ off the diagonal

Fix $y\in(0,1)$ and write $G(x):=\omega(x,y)$.

- **Lower branch** ($x<y$): $G(x)=\dfrac{\ln y}{y^2}\,x$ is a constant multiple of
  $u_L=x$, so $L G=0$ on $(0,y)$.
- **Upper branch** ($x>y$): $G(x)=\dfrac{1}{y^2}\,x\ln x$ is a constant multiple
  of $u_R=x\ln x$, so $L G=0$ on $(y,1)$.

Thus $G$ is a classical solution of $LG=0$ on each side of $x=y$. (Near the
singular endpoint $x=0$ the lower branch is $\propto x\to 0$: $\omega(\cdot,y)$ is
continuous and bounded there, hence locally integrable, so the distribution it
defines makes sense.)

### Step 2 — $\omega$ is continuous across the diagonal $x=y$

From the two branches at $x=y$:
$$G(y^-)=\frac{y\ln y}{y^2}=\frac{\ln y}{y},\qquad
G(y^+)=\frac{y\ln y}{y^2}=\frac{\ln y}{y}.$$
They agree, so $G$ is continuous at $x=y$. Continuity means $G'$ (as a
distribution) has **no** delta — only a possible jump as an ordinary function.

### Step 3 — the derivative jump is $1/y^2$

Differentiate each branch in $x$:
$$G'(x)=\frac{\ln y}{y^2}\ \ (x<y),\qquad
G'(x)=\frac{\ln x+1}{y^2}\ \ (x>y).$$
The one-sided limits at $x=y$ are
$$G'(y^-)=\frac{\ln y}{y^2},\qquad G'(y^+)=\frac{\ln y+1}{y^2},$$
so the jump is
$$[G']_y:=G'(y^+)-G'(y^-)=\frac{(\ln y+1)-\ln y}{y^2}=\frac{1}{y^2}.$$

### Step 4 — assemble the distributional identity $L_xG=\delta(x-y)$

Because $G$ is continuous with a single corner at $x=y$, its distributional
derivatives are
$$G'=\{G'\}\quad(\text{a regular function, no delta}),\qquad
G''=\{G''\}+[G']_y\,\delta(x-y),$$
where $\{\,\cdot\,\}$ denotes the classical (a.e.-defined) derivative. Therefore
$$L_xG=x^2G''-xG'+G
=\underbrace{\big(x^2\{G''\}-x\{G'\}+G\big)}_{=\,0\ \text{a.e. by Step 1}}
+\,x^2\,[G']_y\,\delta(x-y).$$
The regular part vanishes identically (each branch solves $LG=0$). For the
singular part, use $x^2\,\delta(x-y)=y^2\,\delta(x-y)$ together with Step 3:
$$x^2[G']_y\,\delta(x-y)=y^2\cdot\frac{1}{y^2}\,\delta(x-y)=\delta(x-y).$$
Hence
$$\boxed{\,L_x\,\omega(x,y)=\delta(x-y)\quad\text{in }\mathcal D'(0,1),\ \text{for each fixed }y.\,}$$
So the distribution associated with $\omega$ is a fundamental solution of $L$.
$\blacksquare$

### Cross-check — $\omega$ is the textbook Green's function

With $u_L=x$, $u_R=x\ln x$, the Wronskian is
$$W(x)=u_Lu_R'-u_Ru_L'=x(\ln x+1)-(x\ln x)(1)=x,$$
so $p_2(y)W(y)=y^2\cdot y=y^3$. The standard formula gives
$$\frac{u_L(x_<)\,u_R(x_>)}{p_2(y)W(y)}
=\frac{x_<\,(x_>\ln x_>)}{y^3}
=\begin{cases}\dfrac{x\,(y\ln y)}{y^3}=\dfrac{x\ln y}{y^2}, & x\le y,\\[2mm]
\dfrac{y\,(x\ln x)}{y^3}=\dfrac{x\ln x}{y^2}, & x\ge y,\end{cases}$$
which is exactly the given $\omega$. This both confirms the computation and
explains the $\ln y$/$\ln x$ asymmetry: the logarithm rides on $u_R$ evaluated at
the *larger* argument $x_>$.

## What Connects

**To Euler equations and repeated indicial roots.** The whole structure is
dictated by the double root $r=1$ of $(r-1)^2=0$. Repeated roots of the indicial
equation are the source of $\ln$-type second solutions throughout ODE theory
(Frobenius method, resonance), and here they are what gives the Green's function
its logarithmic kernel.

**To Sturm–Liouville Green's functions.** The recipe
$G=u_L(x_<)u_R(x_>)/(p_2W)$ is the general construction of the Green's function
for a second-order operator: pick the homogeneous solution satisfying each
boundary condition, normalize by the leading coefficient times the Wronskian. The
selection $u_L=x$ (regular at the singular endpoint $x=0$) is the analogue of
imposing a boundary condition at a regular-singular point — exactly the
"subdominant solution" choice familiar from boundary-value problems on degenerate
domains.

**To distributional jump formulas.** The mechanism "continuity $\Rightarrow$ no
delta in $G'$; corner $\Rightarrow$ delta in $G''$ with weight $[G']$" is the
one-dimensional prototype of how fundamental solutions of differential operators
acquire their singularities, and the factor $x^2\delta(x-y)=y^2\delta(x-y)$ is
the simplest instance of localizing a variable coefficient onto the diagonal —
the same move that appears for variable-coefficient elliptic operators and their
parametrices.

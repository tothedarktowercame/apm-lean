<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96J02: A second-order IVP and its Volterra integral equation — equivalence, and uniqueness on a short interval

We are given $g$ continuous on $\mathbb R^2$, constants $\alpha,\beta\in\mathbb R$,
the initial-value problem
$$x''(t)=g(t,x(t)),\qquad x(0)=\alpha,\ x'(0)=\beta, \tag{IVP}$$
and the Volterra integral equation
$$y(t)=\int_0^t(t-s)\,g(s,y(s))\,ds+\alpha+\beta t. \tag{V}$$
We must produce $T>0$ such that a $C^2$ solution $x$ of (IVP) and a continuous
solution $y$ of (V) on $[0,T]$ must coincide.

## Why It's Hard

- **Two different formulations must be identified.** (IVP) is a differential
  equation; (V) is an integral equation. Showing they have the *same* solutions
  requires real calculus in both directions: a Fubini interchange to collapse a
  double integral into the single kernel $(t-s)$, and a Leibniz/FTC
  differentiation of a parameter integral to go back. The kernel $(t-s)$ is not
  decorative — it is exactly the **second-order Green's function / Taylor
  remainder**, and recognizing $x(t)=\alpha+\beta t+\int_0^t(t-s)x''(s)\,ds$ is
  the crux of the equivalence.
- **Uniqueness is NOT free from continuity — this is the trap.** With $g$ merely
  continuous, Peano's theorem gives *existence* but uniqueness can genuinely
  **fail**, so the literal statement "$x=y$" is false as written. The real
  content is the uniqueness half of Picard–Lindelöf, which needs a Lipschitz
  condition; the technical heart is a contraction/Gronwall estimate on a short
  interval, plus confining the solutions to a compact box where that Lipschitz
  control is available.
- **The role of $T$.** $T$ must be chosen from the data $(g,\alpha,\beta)$ alone,
  *before* quantifying over the solutions $x,y$ — so one needs an a priori bound
  keeping every solution inside a fixed box on $[0,T]$.

## The Key Insight

**(V) is literally (IVP) integrated twice against the Green's kernel $(t-s)$.**
Integrating $x''=g$ once gives $x'(t)=\beta+\int_0^t g\,ds$; integrating again and
swapping the order of integration turns the double integral into
$\int_0^t(t-s)g(s,x(s))\,ds$ — which is exactly (V). So a function solves (IVP)
**iff** it solves (V); the two are the same equation. Viewing both $x$ and $y$ as
fixed points of the single Volterra operator
$$(\mathcal Ty)(t)=\alpha+\beta t+\int_0^t(t-s)\,g(s,y(s))\,ds,$$
uniqueness becomes the statement that $\mathcal T$ is a **contraction** on a short
interval — with contraction factor $\tfrac{LT^2}{2}$ when $g$ is Lipschitz in its
second variable with constant $L$. That Lipschitz hypothesis is precisely what
"$x=y$" requires.

## Complete Proof

**Standing hypothesis for uniqueness.** Beyond continuity we use that $g$ is
**locally Lipschitz in its second argument**: on each compact box
$K=[0,a]\times[\alpha-b,\alpha+b]$ there is $L=L(K)$ with
$|g(s,u)-g(s,v)|\le L|u-v|$. (See the closing remark for why pure continuity is
insufficient.) The equivalence in Steps 1–2 needs only continuity.

### Step 1 — (IVP) $\Rightarrow$ (V)

Let $x\in C^2([0,T])$ solve (IVP). Integrating $x''(s)=g(s,x(s))$ from $0$ to
$t$ and using $x'(0)=\beta$,
$$x'(t)=\beta+\int_0^t g(s,x(s))\,ds.$$
Integrating once more from $0$ to $t$ and using $x(0)=\alpha$,
$$x(t)=\alpha+\beta t+\int_0^t\!\!\int_0^\tau g(s,x(s))\,ds\,d\tau.$$
The double integral is over the triangle $\{0\le s\le\tau\le t\}$; by Fubini
(the integrand is continuous),
$$\int_0^t\!\!\int_0^\tau g(s,x(s))\,ds\,d\tau=\int_0^t\!\!\left(\int_s^t d\tau\right)g(s,x(s))\,ds=\int_0^t(t-s)\,g(s,x(s))\,ds.$$
Hence $x(t)=\alpha+\beta t+\int_0^t(t-s)g(s,x(s))\,ds$: $x$ solves (V). $\checkmark$

### Step 2 — (V) $\Rightarrow$ (IVP) (so any Volterra solution is automatically $C^2$)

Let $y\in C([0,T])$ solve (V). Put $h(s):=g(s,y(s))$, continuous on $[0,T]$.
First, $y(0)=\alpha$. Split the kernel,
$$\int_0^t(t-s)h(s)\,ds=t\int_0^t h(s)\,ds-\int_0^t s\,h(s)\,ds,$$
and differentiate in $t$ (product rule + FTC):
$$\frac{d}{dt}\!\left[t\!\int_0^t h\right]=\int_0^t h+t\,h(t),\qquad
\frac{d}{dt}\!\int_0^t s\,h\,ds=t\,h(t),$$
so the two $t\,h(t)$ terms cancel and
$$y'(t)=\beta+\int_0^t h(s)\,ds=\beta+\int_0^t g(s,y(s))\,ds.$$
Thus $y'$ exists and is continuous, with $y'(0)=\beta$. Since $h$ is continuous,
the FTC gives $y''(t)=h(t)=g(t,y(t))$, so $y\in C^2$ and $y$ solves (IVP).
$\checkmark$

**Conclusion of the equivalence:** (IVP) and (V) have exactly the same solutions
on any interval. In particular the given $x$ satisfies (V) (Step 1), and the given
$y$ satisfies (IVP) (Step 2); both are fixed points of $\mathcal T$.

### Step 3 — choosing $T$: confine all solutions to one box

Fix $b>0$ and let $K=[0,1]\times[\alpha-b,\alpha+b]$, $M:=\max_K|g|$, and let $L$
be the Lipschitz constant of $g$ on $K$. Choose
$$T\le 1\quad\text{small enough that}\quad |\beta|T+\tfrac{M}{2}T^2\le b
\quad\text{and}\quad \tfrac{L}{2}T^2<1. \tag{$\ast$}$$
This $T$ depends only on $g,\alpha,\beta,b$. Any solution $z$ of (V) satisfies,
as long as it stays in the strip,
$$|z(t)-\alpha|\le|\beta|t+\int_0^t(t-s)|g(s,z(s))|\,ds\le|\beta|T+\tfrac{M}{2}T^2\le b,$$
so a standard continuity (bootstrap) argument keeps $z(t)\in[\alpha-b,\alpha+b]$
for all $t\in[0,T]$: the set of $t$ where $z$ stays in the closed strip is closed,
and the strict estimate above keeps it open, so it is all of $[0,T]$. Applying
this to both $x$ and $y$, both graphs lie in $K$ on $[0,T]$.

### Step 4 — uniqueness on $[0,T]$, hence $x=y$

Both $x,y$ satisfy (V) and lie in $K$. Let $u=x-y$. Subtracting,
$$u(t)=\int_0^t(t-s)\big[g(s,x(s))-g(s,y(s))\big]\,ds,$$
so with the Lipschitz bound on $K$,
$$|u(t)|\le L\int_0^t(t-s)\,|u(s)|\,ds\le L\,\Big(\sup_{[0,T]}|u|\Big)\int_0^t(t-s)\,ds
=\tfrac{L t^2}{2}\sup_{[0,T]}|u|.$$
Taking the supremum over $t\in[0,T]$, with $M_0:=\sup_{[0,T]}|u|$,
$$M_0\le \tfrac{L}{2}T^2\,M_0.$$
Since $\tfrac{L}{2}T^2<1$ by $(\ast)$, this forces $M_0=0$, i.e. $u\equiv0$ and
$$\boxed{\,x\equiv y\ \text{ on }[0,T].\,}$$
$\blacksquare$

*(Equivalent contraction phrasing.* On $C([0,T])$ with the sup norm,
$\|\mathcal Ty_1-\mathcal Ty_2\|_\infty\le\tfrac{L}{2}T^2\,\|y_1-y_2\|_\infty$, so
$\mathcal T$ is a contraction and has a unique fixed point; $x$ and $y$ are both
fixed points, hence equal. With the weighted norm
$\|u\|_\lambda=\sup_t e^{-\lambda t}|u(t)|$ one gets a contraction for large
$\lambda$ on **any** $[0,T]$, so under a global Lipschitz bound uniqueness holds on
the whole interval, not merely a short one.)*

### Remark — why continuity alone is not enough

The conclusion genuinely requires more than continuity of $g$. Take
$g(t,x)=\sqrt{|x|}$ and $\alpha=\beta=0$. Then $x\equiv0$ solves (IVP), and so does
$x(t)=t^4/144$, since $x''=t^2/12=\sqrt{t^4/144}$. By the equivalence (Steps 1–2)
both also solve (V). Thus a continuous-only $g$ can produce $x\neq y$, and Peano's
existence theorem cannot be upgraded to uniqueness without a condition such as
local Lipschitz. The statement of the problem is exactly the **local uniqueness
theorem**, and the Lipschitz hypothesis used above is what makes it true.

## What Connects

**To Picard–Lindelöf.** Steps 1–4 are the standard proof of local
existence–uniqueness recast for a second-order equation: reduce to an integral
(Volterra) fixed-point problem and contract. The reduction $x''=g\rightsquigarrow$
Volterra is the second-order analogue of the first-order
$x'=f\rightsquigarrow x(t)=x_0+\int_0^t f$.

**To Green's functions and Taylor's theorem.** The kernel $(t-s)$ is the Green's
function of $\frac{d^2}{dt^2}$ with the initial conditions built in:
$x(t)=\alpha+\beta t+\int_0^t(t-s)x''(s)\,ds$ is precisely Taylor's formula with
integral remainder. The same construction with a length-$k$ kernel
$\frac{(t-s)^{k-1}}{(k-1)!}$ reduces a $k$-th order IVP to a Volterra equation.

**To Volterra operators and quasinilpotency.** The operator $\mathcal T$ has a
*Volterra* (causal, lower-triangular) structure: its iterated kernels carry the
factorially small factor $\tfrac{(LT)^n}{n!}$, so $\mathcal T^n$ is eventually a
contraction regardless of $L$ and $T$. This is why uniqueness for Volterra
equations is robust — the integral operator is quasinilpotent (spectral radius
$0$) — and why the weighted-norm trick upgrades short-interval uniqueness to the
whole interval.

**To Peano vs. Picard.** The $\sqrt{|x|}$ counterexample is the canonical
separator between Peano (continuity $\Rightarrow$ existence) and Picard
(Lipschitz $\Rightarrow$ uniqueness); it is worth carrying explicitly into any
formalization, since the clean theorem requires the Lipschitz hypothesis that the
continuous-only statement omits.

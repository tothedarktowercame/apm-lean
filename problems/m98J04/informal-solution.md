<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98J04: The Euler–Lagrange equation, and why the straight line is the shortest path

## Why It's Hard

The problem has two faces, and the second is sneakier than it looks:

- **(a) Deriving the Euler equation** is a rite of passage in the calculus of variations, and the rigor lives in two easily-skipped steps: (i) the boundary terms in the integration by parts vanish *because the variation $\eta$ is fixed at the endpoints* — this is where the constraints $y(a)=\alpha,\ y(b)=\beta$ enter; and (ii) passing from "$\int(\cdots)\eta=0$ for all $\eta$" to "$(\cdots)=0$" is **not** automatic — it requires the **fundamental lemma of the calculus of variations**, which must be invoked (and ideally justified), not waved at.
- **(b) Shortest distance = straight line** is the classic application, but proving it *fully* means more than finding a stationary curve. The Euler equation only produces a **critical point**; to conclude it is the *minimum* one must verify the arc-length integrand is **convex** in $y'$, so the functional is convex and the critical point is the global minimizer. Stopping at "$y'=\text{const}\Rightarrow$ line" answers "which curve is stationary," not "why it is shortest."

The unifying difficulty is keeping straight what the Euler equation does and does not deliver: it is a *necessary* condition for an extremum, made *sufficient* here by convexity.

## The Key Insight

A minimizer $y$ makes the first variation vanish in every admissible direction $\eta$ (with $\eta(a)=\eta(b)=0$):
$$
0=\frac{d}{d\epsilon}\Big|_{\epsilon=0}\!\int_a^b F(x,y+\epsilon\eta,y'+\epsilon\eta')\,dx
=\int_a^b\Big(F_y-\frac{d}{dx}F_{y'}\Big)\eta\,dx,
$$
after integrating the $F_{y'}\eta'$ term by parts (boundary terms die because $\eta$ vanishes at the ends). Since $\eta$ is arbitrary, the **fundamental lemma** forces the **Euler–Lagrange equation**
$$
\boxed{\,F_y-\frac{d}{dx}F_{y'}=0\,}.
$$
For arc length, $F(x,y,y')=\sqrt{1+y'^2}$ depends on **neither $x$ nor $y$**, so $F_y=0$ and the Euler equation collapses to
$$
\frac{d}{dx}F_{y'}=0\ \Longrightarrow\ F_{y'}=\frac{y'}{\sqrt{1+y'^2}}=\text{const}\ \Longrightarrow\ y'=\text{const},
$$
a straight line. Convexity of $y'\mapsto\sqrt{1+y'^2}$ then upgrades "critical" to "global minimum."

## Complete Proof

### Part (a): derivation of the Euler equation

Let $y$ be a (twice continuously differentiable) minimizer of
$$
J[y]=\int_a^b F\big(x,y(x),y'(x)\big)\,dx,\qquad y(a)=\alpha,\ y(b)=\beta,
$$
where $F$ is assumed $C^2$ in its arguments. Let $\eta\in C^1([a,b])$ be any **admissible variation**, meaning $\eta(a)=\eta(b)=0$; then for every $\epsilon\in\mathbb{R}$ the curve $y+\epsilon\eta$ also satisfies the boundary conditions, so it is a competitor. Define
$$
\phi(\epsilon)=J[y+\epsilon\eta]=\int_a^b F\big(x,\,y+\epsilon\eta,\,y'+\epsilon\eta'\big)\,dx .
$$
Since $y$ minimizes $J$, the real function $\phi$ has a minimum at $\epsilon=0$, hence $\phi'(0)=0$. Differentiating under the integral sign (legitimate by the $C^2$ assumption and compactness of $[a,b]$) and using the chain rule,
$$
\phi'(\epsilon)=\int_a^b\Big[F_y\big(x,y+\epsilon\eta,y'+\epsilon\eta'\big)\,\eta+F_{y'}\big(x,y+\epsilon\eta,y'+\epsilon\eta'\big)\,\eta'\Big]\,dx,
$$
so at $\epsilon=0$,
$$
0=\phi'(0)=\int_a^b\big[F_y\,\eta+F_{y'}\,\eta'\big]\,dx .
$$
Integrate the second term by parts:
$$
\int_a^b F_{y'}\,\eta'\,dx=\big[F_{y'}\,\eta\big]_a^b-\int_a^b\frac{d}{dx}\big(F_{y'}\big)\,\eta\,dx
=-\int_a^b\frac{d}{dx}\big(F_{y'}\big)\,\eta\,dx,
$$
the boundary term vanishing because $\eta(a)=\eta(b)=0$. Therefore
$$
0=\int_a^b\Big[F_y-\frac{d}{dx}F_{y'}\Big]\,\eta(x)\,dx\qquad\text{for every admissible }\eta. \tag{$\ast$}
$$

**Fundamental lemma of the calculus of variations.** *If $g\in C([a,b])$ satisfies $\int_a^b g\,\eta\,dx=0$ for all $\eta\in C^1$ with $\eta(a)=\eta(b)=0$, then $g\equiv0$.* Indeed, if $g(x_0)\ne0$ at some interior $x_0$ — say $g(x_0)>0$ — then by continuity $g>0$ on some $(x_0-\delta,x_0+\delta)\subset(a,b)$. Choose the bump $\eta(x)=\big[(x-x_0+\delta)(x_0+\delta-x)\big]^2$ on that interval and $\eta=0$ elsewhere; this $\eta$ is $C^1$, admissible, nonnegative, and positive on the interval, so $\int_a^b g\eta\,dx>0$, contradicting the hypothesis. Hence $g\equiv0$.

Applying the lemma to $g=F_y-\frac{d}{dx}F_{y'}$ (continuous, by $y\in C^2$) in $(\ast)$ yields the **Euler–Lagrange equation**
$$
\boxed{\,F_y-\frac{d}{dx}F_{y'}=0\quad\text{on }[a,b].\,}\qquad\checkmark
$$

### Part (b): the shortest plane curve between two points is a straight line

Let the two points be $P=(a,\alpha)$ and $Q=(b,\beta)$ with $a<b$. A curve given by a graph $y(x)$ joining them ($y(a)=\alpha$, $y(b)=\beta$) has arc length
$$
L[y]=\int_a^b\sqrt{1+y'(x)^2}\,dx,
$$
so the natural choice is $F(x,y,y')=\sqrt{1+y'^2}$. This $F$ depends only on $y'$:
$$
F_y=0,\qquad F_{y'}=\frac{y'}{\sqrt{1+y'^2}} .
$$
The Euler equation $F_y-\frac{d}{dx}F_{y'}=0$ becomes $\frac{d}{dx}F_{y'}=0$, i.e. $F_{y'}$ is constant along the extremal:
$$
\frac{y'}{\sqrt{1+y'^2}}=C .
$$
Solving: squaring gives $y'^2=C^2(1+y'^2)$, so $y'^2(1-C^2)=C^2$ (note $|C|<1$ is forced, as the left side $\frac{y'}{\sqrt{1+y'^2}}\in(-1,1)$), hence
$$
y'=\frac{C}{\sqrt{1-C^2}}=:m\quad(\text{a constant})\ \Longrightarrow\ y(x)=mx+c .
$$
The extremal is a **straight line**. The boundary conditions determine it uniquely:
$$
m=\frac{\beta-\alpha}{b-a},\qquad c=\alpha-ma,\qquad\text{i.e.}\quad y(x)=\alpha+\frac{\beta-\alpha}{b-a}(x-a),
$$
the segment $\overline{PQ}$, of length $L=\sqrt{(b-a)^2+(\beta-\alpha)^2}=|PQ|$, the Euclidean distance.

**It is a genuine minimum (not merely stationary).** The integrand $f(p)=\sqrt{1+p^2}$ is **strictly convex** in $p=y'$:
$$
f''(p)=\frac{1}{(1+p^2)^{3/2}}>0 .
$$
For a functional $L[y]=\int_a^b f(y')\,dx$ with $f$ convex, $L$ is convex on the admissible (affine) set, and any solution of the Euler equation is a **global minimizer**. Concretely, for the line $\bar y$ and any competitor $y=\bar y+\eta$ with $\eta(a)=\eta(b)=0$, convexity gives $f(\bar y'+\eta')\ge f(\bar y')+f'(\bar y')\eta'$, so
$$
L[y]-L[\bar y]\ge\int_a^b f'(\bar y')\,\eta'\,dx=f'(m)\int_a^b\eta'\,dx=f'(m)\big[\eta\big]_a^b=0,
$$
using that $\bar y'=m$ is constant and $\eta(a)=\eta(b)=0$. Hence $L[y]\ge L[\bar y]$ for every competitor: **the straight segment is the shortest path** between $P$ and $Q$. $\qquad\blacksquare$

### Remark — necessity, sufficiency, and the role of the integrand's structure

The Euler equation is a *necessary* condition: it identifies stationary curves. What makes part (b) a complete proof of minimality is the *convexity* of $F$ in $y'$, which is the simplest sufficient condition (and the second-variation/Jacobi theory degenerates to it here, since $F_{yy}=F_{yy'}=0$). Two structural simplifications were exploited: $F$ independent of $y$ gave $F_y=0$, and $F$ independent of $x$ would alternatively allow the **Beltrami first integral** $F-y'F_{y'}=\text{const}$ — either route yields $y'=\text{const}$. The same machinery, with a different $F$, produces geodesics on surfaces, brachistochrones ($F=\sqrt{(1+y'^2)/y}$), and minimal surfaces of revolution ($F=y\sqrt{1+y'^2}$, catenary) — the straight line is the flat prototype where the metric integrand $\sqrt{1+y'^2}$ has no $x$- or $y$-dependence at all.

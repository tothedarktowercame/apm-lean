<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J09: The Laplace transform of an Lᵖ function is holomorphic on the right half-plane

## Why It's Hard

The function $F(z)=\int_0^\infty f(t)e^{-tz}\,dt$ is handed to us as an integral that *depends on a complex parameter* $z$, and "holomorphic" is a property that must be **extracted** from that integral — it is not visible by inspection. Two layers of difficulty stack up:

1. **Even convergence is nontrivial.** The datum is only $f\in L^p$ with $1<p<\infty$, not $f\in L^1$. So $f(t)e^{-tz}$ has no reason to be integrable from $f$ alone — it is integrable *only because* the exponential factor $e^{-tz}$ supplies decay. Quantifying that decay requires **Hölder's inequality** against the conjugate exponent $q$, and the relevant norm $\|e^{-tz}\|_{L^q}$ is finite **precisely when $\Re z>0$** (and $q<\infty$, i.e. $p>1$). The right half-plane is not an arbitrary domain; it is exactly where the integral makes sense.

2. **Holomorphy is an interchange-of-limits statement.** For each fixed $t$ the integrand $z\mapsto e^{-tz}$ is entire — the only thing standing between us and holomorphy of $F$ is the right to interchange the contour integral (or the derivative) in $z$ with the integral in $t$. All the analytic care goes into licensing that swap, and the estimates degrade as $\Re z\downarrow 0$, so one must work locally on half-planes $\{\Re z\ge\delta\}$ where the domination is uniform. The differentiation route additionally has to absorb the factor $t$ coming from $\partial_z e^{-tz}=-t\,e^{-tz}$, which costs a gamma-type integral.

## The Key Insight

For each fixed $t\ge0$, the map $z\mapsto e^{-tz}$ is **entire**. So $F$ inherits holomorphy from the integrand *provided* one may move the analytic operation (a closed-contour integral, via Morera; or a difference quotient, via dominated convergence) inside $\int_0^\infty(\cdot)\,dt$. The license to do so is a single uniform, integrable bound, and **Hölder against $e^{-t\Re z}\in L^q$** delivers it: on any sub-half-plane $\{\Re z\ge\delta\}$,
$$
\int_0^\infty |f(t)|\,e^{-t\delta}\,dt \le \|f\|_p\Big(\int_0^\infty e^{-q\delta t}\,dt\Big)^{1/q}=\|f\|_p\,(q\delta)^{-1/q}<\infty,
$$
finite exactly because $\delta>0$ and $q<\infty$. That bound is uniform in $z$ over the strip, which is all that Morera's theorem (or differentiation under the integral) needs. Holomorphy thus reduces to: *(entire integrand) + (Hölder-supplied domination) ⟹ swap is legal*.

## Complete Proof

Let $H:=\{z\in\mathbb{C}:\Re z>0\}$, and let $q$ be the conjugate exponent, $\tfrac1p+\tfrac1q=1$, so $1<q<\infty$. Write $x:=\Re z$.

### Step 1 — $F$ is well-defined on $H$

Fix $z\in H$, so $x>0$. Since $|e^{-tz}|=e^{-tx}$, Hölder's inequality gives
$$
\int_0^\infty |f(t)e^{-tz}|\,dt=\int_0^\infty |f(t)|\,e^{-tx}\,dt
\le \|f\|_p\Big(\int_0^\infty e^{-qtx}\,dt\Big)^{1/q}
=\|f\|_p\,(qx)^{-1/q}<\infty. \tag{1}
$$
The middle factor is finite because $x>0$ makes $t\mapsto e^{-tx}$ lie in $L^q(0,\infty)$ (here $q<\infty$, equivalently $p>1$, is used). Hence the defining integral converges absolutely and $F(z)$ is well-defined for every $z\in H$.

### Step 2 — $F$ is continuous on $H$

Fix $z_0\in H$ and set $\delta:=\tfrac12\Re z_0>0$. For $z$ in the neighborhood $U:=\{\Re z\ge\delta\}$ of $z_0$ and all $t\ge0$,
$$
|f(t)e^{-tz}| = |f(t)|\,e^{-t\Re z}\le |f(t)|\,e^{-t\delta}=:\Psi(t),
$$
and $\Psi\in L^1(0,\infty)$ by the estimate $(1)$ with $x=\delta$. If $z_n\to z_0$ in $U$, then $f(t)e^{-tz_n}\to f(t)e^{-tz_0}$ pointwise and is dominated by $\Psi$, so the **Dominated Convergence Theorem** gives $F(z_n)\to F(z_0)$. Thus $F$ is continuous on $H$.

### Step 3 — Holomorphy via Morera's theorem

Let $\Delta\subset H$ be any closed (solid) triangle. As a compact subset of the open half-plane, $\Delta$ satisfies $\delta:=\min_{z\in\Delta}\Re z>0$, and its boundary $\partial\Delta$ has finite length $L$. Consider
$$
\oint_{\partial\Delta} F(z)\,dz=\oint_{\partial\Delta}\Big(\int_0^\infty f(t)e^{-tz}\,dt\Big)dz.
$$
The double integral is **absolutely convergent**:
$$
\int_{\partial\Delta}\int_0^\infty |f(t)|\,e^{-t\Re z}\,dt\,|dz|
\le L\cdot\|f\|_p\,(q\delta)^{-1/q}<\infty,
$$
using $(1)$ with $x=\Re z\ge\delta$ uniformly along $\partial\Delta$. **Fubini's theorem** therefore permits interchanging the order:
$$
\oint_{\partial\Delta} F(z)\,dz=\int_0^\infty f(t)\Big(\oint_{\partial\Delta} e^{-tz}\,dz\Big)dt.
$$
For each fixed $t$, the function $z\mapsto e^{-tz}$ is entire, so by the Cauchy–Goursat theorem $\oint_{\partial\Delta}e^{-tz}\,dz=0$. Hence
$$
\oint_{\partial\Delta} F(z)\,dz=\int_0^\infty f(t)\cdot 0\,dt=0
$$
for **every** triangle $\Delta\subset H$. Since $F$ is continuous on $H$ (Step 2) and its integral around every triangle vanishes, **Morera's theorem** yields that $F$ is holomorphic on $H$. $\qquad\blacksquare$

### Step 4 — The derivative, explicitly (differentiation under the integral)

The same domination identifies $F'$. Fix $z_0\in H$, $x_0=\Re z_0$, and $\delta=x_0/2$. For $0<|h|\le\delta$,
$$
\frac{F(z_0+h)-F(z_0)}{h}=\int_0^\infty f(t)e^{-tz_0}\,\frac{e^{-th}-1}{h}\,dt .
$$
Pointwise $\dfrac{e^{-th}-1}{h}\to -t$ as $h\to0$, and using $|e^{w}-1|\le|w|e^{|w|}$ with $w=-th$,
$$
\Big|f(t)e^{-tz_0}\tfrac{e^{-th}-1}{h}\Big|\le |f(t)|\,e^{-tx_0}\cdot t\,e^{t|h|}\le t\,|f(t)|\,e^{-t\delta}.
$$
This dominating function is integrable, again by Hölder: $\int_0^\infty t|f(t)|e^{-t\delta}\,dt\le\|f\|_p\big(\int_0^\infty (te^{-t\delta})^q\,dt\big)^{1/q}$, and $\int_0^\infty t^q e^{-q\delta t}\,dt=\dfrac{\Gamma(q+1)}{(q\delta)^{q+1}}<\infty$. By dominated convergence,
$$
F'(z)=-\int_0^\infty t\,f(t)\,e^{-tz}\,dt,\qquad z\in H,
$$
which exists throughout $H$ — an independent confirmation that $F$ is holomorphic, with this formula for its derivative.

### Remark — why $\Re z>0$ is the exact domain

Both the existence of $F$ and the domination rest on $e^{-t\Re z}\in L^q(0,\infty)$, which holds **iff** $\Re z>0$. On the imaginary axis $\Re z=0$ the factor $e^{-tz}$ has modulus $1$ and the integral need not converge for $f\in L^p$, $p>1$ — so $H$ is not just a convenient domain but the natural one. The role of $1<p<\infty$ is twofold: $p>1$ gives a *finite* conjugate exponent $q$, so $\|e^{-tz}\|_q$ is computable and finite; and the structure is exactly a Hölder pairing of $f\in L^p$ against the smooth, rapidly decaying $L^q$ kernels $e^{-tz}$ and $te^{-tz}$. (For $p=1$ one would instead pair $L^1$ against $L^\infty$, bounding by $\|f\|_1$; the same conclusion holds, by the same Morera argument.)

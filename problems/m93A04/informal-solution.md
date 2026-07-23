<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93A04: Fréchet differentiability of a Urysohn integral operator on $C[0,1]$ — the derivative $I-T_x$ and its invertibility

## Why It's Hard

The map $F(x)(t)=x(t)-\int_0^1 K(t,x(s))\,ds$ is a nonlinear (Urysohn) integral operator on the *infinite-dimensional* Banach space $C[0,1]$, and the problem is deliberately open-ended: it asks the solver to **supply the hypotheses** that make each claim true, not merely to verify them. Three things have to be gotten right:

- **The right assumption on $K$.** For $F$ to even land in $C[0,1]$ one needs continuity of $K$; for $F$ to be *differentiable* one needs $K$ to be $C^1$ in its second slot with a *jointly continuous* partial $K_u$. Guessing too little (only continuity) or too much (full $C^1$ in both variables, or global Lipschitz) both miss the mark.
- **Differentiating under the integral, rigorously.** The candidate derivative — "differentiate the integrand in $u$" — is easy to *write*; the work is proving the remainder is $o(\|h\|)$ **uniformly in $t$**, which is exactly where the sup-norm on $C[0,1]$ bites. The engine is uniform continuity of $K_u$ on a compact set, and one must identify that compact set ($x$ has bounded range; perturbations $h$ are small).
- **Reading off the structure of $F'$.** The derivative turns out to be $F'(x)=I-T_x$ with $T_x$ a Fredholm integral operator of *continuous kernel*, hence **compact**. Invertibility of $I-(\text{compact})$ is then governed by the Fredholm alternative / Neumann series, and the "further weak hypothesis" the problem hints at is a smallness condition on $K_u$.

The deeper point — which the phrasing nudges toward — is that this is precisely the **implicit-function-theorem setup** for the integral equation $x=\int_0^1K(t,x(s))\,ds$: "$F'(x)$ invertible" is the IFT hypothesis.

## The Key Insight

Write $F=I-G$, where $G(x)(t)=\int_0^1K(t,x(s))\,ds$ is the nonlinear part. Under the assumption that **$K(t,u)$ and $K_u(t,u):=\partial_u K(t,u)$ are continuous on $[0,1]\times\mathbb{R}$**, the operator $G$ is Fréchet differentiable with derivative obtained by differentiating the integrand:
$$
G'(x)h(t)=\int_0^1 K_u\big(t,x(s)\big)\,h(s)\,ds,\qquad\text{so}\qquad
\boxed{\,F'(x)h(t)=h(t)-\int_0^1 K_u\big(t,x(s)\big)\,h(s)\,ds\,}.
$$
Thus $F'(x)=I-T_x$ where $T_x$ is the **linear Fredholm operator with continuous kernel** $\kappa_x(t,s)=K_u(t,x(s))$. Two facts close the problem:

1. $T_x$ is **compact** on $C[0,1]$ (continuous kernel $\Rightarrow$ Arzelà–Ascoli), so $I-T_x$ is invertible **iff $1$ is not an eigenvalue of $T_x$** (Fredholm alternative).
2. The cleanest *weak hypothesis* forcing this is a **contraction condition**: if $\sup_{t,u}|K_u(t,u)|\le c<1$, then $\|T_x\|\le c<1$, so $F'(x)=I-T_x$ is invertible at **every** $x$, with inverse the convergent Neumann series $\sum_{n\ge0}T_x^{\,n}$.

The whole problem is the differentiability and invertibility of "identity minus a compact integral operator" — the canonical structure behind nonlinear integral equations.

## Complete Proof

### The appropriate assumption on $K$

**Assume:** $K:[0,1]\times\mathbb{R}\to\mathbb{R}$ is continuous, and is continuously differentiable in its second variable, with the partial derivative $K_u(t,u)=\dfrac{\partial K}{\partial u}(t,u)$ **jointly continuous** on $[0,1]\times\mathbb{R}$.

This is exactly enough: continuity of $K$ makes $F$ map $C[0,1]$ into itself, and joint continuity of $K_u$ makes $F$ Fréchet differentiable.

**$F$ maps $C[0,1]$ into $C[0,1]$.** Fix $x\in C[0,1]$. For each $t$, $s\mapsto K(t,x(s))$ is continuous, so the integral exists. If $t_n\to t$, then $K(t_n,x(s))\to K(t,x(s))$ for each $s$, and since $K$ is continuous on the compact set $[0,1]\times[-\|x\|_\infty,\|x\|_\infty]$ it is bounded there, so by dominated (or uniform) convergence $\int_0^1K(t_n,x(s))\,ds\to\int_0^1K(t,x(s))\,ds$. Hence $G(x)\in C[0,1]$ and $F(x)=x-G(x)\in C[0,1]$.

### Fréchet differentiability and the formula for $F'$

Fix $x\in C[0,1]$ and let $M=\|x\|_\infty$. Define the linear operator
$$
L h(t)=h(t)-\int_0^1 K_u\big(t,x(s)\big)\,h(s)\,ds .
$$

**$L$ is bounded and linear.** Linearity is clear. The kernel $\kappa_x(t,s)=K_u(t,x(s))$ is continuous on $[0,1]^2$, hence bounded, say $|\kappa_x|\le B$. Then $Lh\in C[0,1]$ (same continuity argument as for $G$) and
$$
\|Lh\|_\infty\le\|h\|_\infty+\sup_t\int_0^1|\kappa_x(t,s)|\,|h(s)|\,ds\le(1+B)\,\|h\|_\infty,
$$
so $L\in\mathcal{B}(C[0,1])$. We claim $F'(x)=L$.

**The remainder is $o(\|h\|)$.** For $h\in C[0,1]$ with $\|h\|_\infty\le1$,
$$
F(x+h)(t)-F(x)(t)-Lh(t)
=-\int_0^1\!\Big[K\big(t,x(s)+h(s)\big)-K\big(t,x(s)\big)-K_u\big(t,x(s)\big)h(s)\Big]ds .
$$
Call the bracket $R(t,s)$. By the fundamental theorem of calculus applied to $\theta\mapsto K(t,x(s)+\theta h(s))$,
$$
R(t,s)=\int_0^1\Big[K_u\big(t,x(s)+\theta h(s)\big)-K_u\big(t,x(s)\big)\Big]h(s)\,d\theta,
$$
so
$$
|R(t,s)|\le|h(s)|\,\sup_{0\le\theta\le1}\Big|K_u\big(t,x(s)+\theta h(s)\big)-K_u\big(t,x(s)\big)\Big|. \tag{$\dagger$}
$$
Now invoke **uniform continuity of $K_u$** on the compact set $Q=[0,1]\times[-M-1,\,M+1]$. Given $\varepsilon>0$ there is $\delta\in(0,1]$ such that
$$
(t,u),(t,u')\in Q,\ |u-u'|<\delta\ \Longrightarrow\ |K_u(t,u)-K_u(t,u')|<\varepsilon .
$$
Suppose $\|h\|_\infty<\delta$. For every $s,\theta,t$, the points $(t,x(s))$ and $(t,x(s)+\theta h(s))$ lie in $Q$ (since $|x(s)|\le M$ and $\theta|h(s)|\le\|h\|_\infty<1$), and they differ in the second coordinate by $\theta|h(s)|\le\|h\|_\infty<\delta$. So $(\dagger)$ gives $|R(t,s)|\le\varepsilon|h(s)|\le\varepsilon\|h\|_\infty$, whence
$$
\big|F(x+h)(t)-F(x)(t)-Lh(t)\big|\le\int_0^1|R(t,s)|\,ds\le\varepsilon\,\|h\|_\infty\qquad(\forall t).
$$
Taking the supremum over $t$,
$$
\frac{\|F(x+h)-F(x)-Lh\|_\infty}{\|h\|_\infty}\le\varepsilon\qquad\text{whenever }0<\|h\|_\infty<\delta .
$$
Since $\varepsilon>0$ was arbitrary, this ratio tends to $0$ as $\|h\|_\infty\to0$. Hence $F$ is **Fréchet differentiable** at $x$ with
$$
F'(x)h(t)=h(t)-\int_0^1 K_u\big(t,x(s)\big)\,h(s)\,ds,
$$
i.e. $F'(x)=I-T_x$, where $\displaystyle T_x h(t)=\int_0^1 K_u(t,x(s))\,h(s)\,ds$. $\qquad\checkmark$

*(One can further check $x\mapsto F'(x)$ is continuous from $C[0,1]$ into $\mathcal{B}(C[0,1])$, using uniform continuity of $K_u$, so $F$ is in fact $C^1$; this is what an implicit-function-theorem application would want.)*

### $T_x$ is compact

The kernel $\kappa_x(t,s)=K_u(t,x(s))$ is continuous on $[0,1]^2$. If $\{h_n\}$ is bounded in $C[0,1]$, $\|h_n\|_\infty\le C$, then $\{T_xh_n\}$ is uniformly bounded ($\|T_xh_n\|_\infty\le BC$) and **equicontinuous**: by uniform continuity of $\kappa_x$, for $|t-t'|$ small, $|\kappa_x(t,s)-\kappa_x(t',s)|<\eta$ uniformly in $s$, so $|T_xh_n(t)-T_xh_n(t')|\le C\eta$. By **Arzelà–Ascoli**, $\{T_xh_n\}$ has a uniformly convergent subsequence. Thus $T_x$ is a **compact** operator on $C[0,1]$.

### Invertibility of $F'(x)=I-T_x$ under a weak hypothesis

**Weak hypothesis (contraction in the second variable).** *Assume there is a constant $c<1$ with*
$$
|K_u(t,u)|\le c\quad\text{for all }(t,u)\in[0,1]\times\mathbb{R}.
$$
(Equivalently: $K(t,\cdot)$ is Lipschitz in $u$ with constant $<1$, uniformly in $t$ — a mild, "weak" smallness condition.)

Then for every $x\in C[0,1]$ the kernel satisfies $|\kappa_x(t,s)|=|K_u(t,x(s))|\le c$, so
$$
\|T_x\|=\sup_{\|h\|_\infty\le1}\,\sup_t\Big|\int_0^1\kappa_x(t,s)h(s)\,ds\Big|\le\sup_t\int_0^1|\kappa_x(t,s)|\,ds\le c<1 .
$$
Because $\|T_x\|<1$, the **Neumann series** $\sum_{n=0}^\infty T_x^{\,n}$ converges in operator norm (it is dominated by the geometric series $\sum c^n=\tfrac1{1-c}$), and its sum is a bounded inverse:
$$
F'(x)^{-1}=(I-T_x)^{-1}=\sum_{n=0}^\infty T_x^{\,n},\qquad \|F'(x)^{-1}\|\le\frac{1}{1-c}.
$$
Hence $F'(x)$ is invertible (a bounded linear bijection of $C[0,1]$) at **every** $x$. $\qquad\blacksquare$

**Sharp criterion (Fredholm alternative).** Even without the smallness bound, since $T_x$ is compact, $I-T_x$ is invertible **iff $1$ is not an eigenvalue of $T_x$**, i.e. iff the homogeneous equation
$$
h(t)=\int_0^1 K_u\big(t,x(s)\big)\,h(s)\,ds
$$
has only the trivial solution $h\equiv0$ in $C[0,1]$. (For a compact operator, injectivity of $I-T_x$ is equivalent to surjectivity and to bounded invertibility — the Riesz–Schauder theory.) The contraction hypothesis $|K_u|\le c<1$ is simply a convenient sufficient condition guaranteeing $1\notin\operatorname{spec}(T_x)$.

### Remark — the implicit-function-theorem picture

The three requests assemble into the standard analysis of the nonlinear integral equation $x(t)=\int_0^1K(t,x(s))\,ds$, i.e. $F(x)=0$. We have shown $F\in C^1$ with $F'(x)=I-T_x$, $T_x$ compact. Where $F'(x_0)$ is invertible — guaranteed under the weak hypothesis $|K_u|<1$, or more generally whenever $1\notin\operatorname{spec}(T_{x_0})$ — the **implicit/inverse function theorem in Banach space** applies: $F$ is a local diffeomorphism near $x_0$, the equation $F(x)=y$ is locally uniquely solvable, and solutions depend smoothly on data. The recurring structural fact, here as throughout integral-equation theory, is that the linearization is **identity minus a compact operator**, for which invertibility is decided by the Fredholm alternative. The model special case $K(t,u)=\lambda\,k(t)\,g(u)$ recovers a classical Hammerstein equation, with $K_u=\lambda k(t)g'(u)$ and invertibility for $|\lambda|$ small.

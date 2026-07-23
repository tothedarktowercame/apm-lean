<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m02J05: Orlicz spaces — convexity of $K_A$, the vector space $L_A$, the Luxemburg norm, and the Young/Hölder inequality

## Why It's Hard

The problem builds the Orlicz space $L_A$ from scratch out of a single Young function and asks one to verify, in order, every structural fact needed to make it a normed space — and then the duality inequality that makes the construction useful. The difficulties are layered:

- **(a)** is easy *once you notice the right two properties of $A$*: $A$ is **convex** (its derivative $\alpha$ is increasing) and **nondecreasing** (its derivative $\alpha\ge 0$). Both are needed, and in this order, to push the triangle inequality through $A$.
- **(b)** is subtle because $K_A$ is **not** a vector space — it is only convex and "solid". A function $u$ may have $\int A(|u|)=\infty$ yet still lie in $L_A$ because some *rescaled* copy $\lambda u$ is integrable. The closure of $L_A$ under addition is therefore not automatic: one must rescale *both* summands to a common factor small enough to land back in $K_A$, and the convexity of part (a) is exactly what makes the rescaled sum integrable.
- **(c)** is the **Luxemburg norm**, defined by an infimum over a sublevel condition rather than an integral. The hard points are that the defining set is nonempty (needs Dominated Convergence), that the infimum is *attained* (needs Fatou — this is what makes part (d) tight), and that the triangle inequality holds (a one-line convexity miracle once the scaling is chosen as $\lambda=\|u\|_A+\|v\|_A$).
- **(d)** is **Young's inequality** $st\le A(s)+\tilde A(t)$ — the statement that $A$ and $\tilde A$ are a *complementary pair* — followed by a normalize-and-integrate step that turns it into Hölder. The factor of $2$ is the signature of the Luxemburg (rather than Orlicz) norm: each of the two integrals contributes a $1$.

## The Key Insight

Everything flows from four properties of the **complementary pair** $A,\tilde A$, none of which require differentiability of $\alpha$:

1. $A$ and $\tilde A$ are convex, nondecreasing, vanish at $0$, and $\to\infty$ — because $A'=\alpha$ and $\tilde A'=\alpha^{-1}$ are nonnegative and increasing.
2. **Solidity/scaling**: $|c|\le 1\Rightarrow A(|cu|)\le A(|u|)$, so $K_A$ is closed under shrinking. This, plus convexity (a), runs part (b).
3. **Attainment**: the Luxemburg sublevel set $\{\lambda>0:\int A(|u|/\lambda)\le 1\}$ is a closed upward ray $[\,\|u\|_A,\infty)$ — closed by Fatou. So $\int A(|u|/\|u\|_A)\le 1$ *exactly*, which is what makes Hölder come out with constant $2$.
4. **Young**: $st\le A(s)+\tilde A(t)$, geometric in nature — the rectangle $[0,s]\times[0,t]$ is covered by the region under $y=\alpha(x)$ and the region left of $x=\alpha^{-1}(y)$, with equality iff $t=\alpha(s)$.

The Luxemburg triangle inequality is the prettiest step: to bound $\|u+v\|_A$, scale by $\lambda=\|u\|_A+\|v\|_A$ and write $|u+v|/\lambda$ as a **convex combination** of $|u|/\|u\|_A$ and $|v|/\|v\|_A$ with weights $\|u\|_A/\lambda,\ \|v\|_A/\lambda$; convexity of $A$ collapses the integral to $\le 1$.

## Complete Proof

Throughout, integrals are over $[0,1]$ with Lebesgue measure, and $A,\tilde A$ are as defined. We first record the properties of $A$ used everywhere.

**Properties of $A$.** Since $\alpha$ is continuous, nonnegative (it increases from $\alpha(0)=0$), and strictly increasing, $A(t)=\int_0^t\alpha(\tau)\,d\tau$ is:

- **finite and continuous** on $[0,\infty)$, with $A(0)=0$;
- **nondecreasing** (indeed strictly increasing for $t>0$), because $A'=\alpha\ge0$;
- **convex** (indeed strictly), because $A'=\alpha$ is increasing;
- **coercive**: $A(t)\to\infty$ as $t\to\infty$ (since $\alpha(\tau)\ge\alpha(1)>0$ for $\tau\ge1$, so $A(t)\ge\alpha(1)(t-1)$).

The identical statements hold for $\tilde A$ with $\alpha^{-1}$ in place of $\alpha$ ($\alpha^{-1}:[0,\infty)\to[0,\infty)$ is also continuous, strictly increasing, $\alpha^{-1}(0)=0$, $\alpha^{-1}\to\infty$).

### Part (a): $K_A$ is convex

Let $u,v\in K_A$ and $\theta\in[0,1]$. For a.e. $x$, the ordinary triangle inequality gives
$$
|\theta u(x)+(1-\theta)v(x)|\le \theta|u(x)|+(1-\theta)|v(x)|.
$$
Since $A$ is **nondecreasing**, applying $A$ preserves this inequality, and since $A$ is **convex**,
$$
A\big(|\theta u+(1-\theta)v|\big)\le A\big(\theta|u|+(1-\theta)|v|\big)\le \theta\,A(|u|)+(1-\theta)\,A(|v|).
$$
Integrating over $[0,1]$,
$$
\int A\big(|\theta u+(1-\theta)v|\big)\,dx \le \theta\!\int A(|u|)\,dx+(1-\theta)\!\int A(|v|)\,dx<\infty,
$$
because both terms on the right are finite. Hence $\theta u+(1-\theta)v\in K_A$, so $K_A$ is convex. $\qquad\checkmark$

We also record the **solidity** of $K_A$: if $w\in K_A$ and $|c|\le 1$, then $|cw|=|c||w|\le|w|$, so $A(|cw|)\le A(|w|)$ (monotonicity) and $\int A(|cw|)\le\int A(|w|)<\infty$; thus $cw\in K_A$. In particular $0\in K_A$ (as $A(0)=0$).

### Part (b): $L_A$ is a vector space

$L_A=\{u\text{ measurable}:\exists\,\lambda\ne0,\ \lambda u\in K_A\}$ is a set of (equivalence classes of) measurable functions; we show it is a linear subspace.

**Zero.** $0\in K_A\subseteq L_A$ (take $\lambda=1$).

**Closed under scalar multiplication.** Let $u\in L_A$ and $c$ a scalar. If $c=0$, then $cu=0\in L_A$. If $c\ne 0$, choose $\lambda\ne0$ with $\lambda u\in K_A$; then $(\lambda/c)(cu)=\lambda u\in K_A$ and $\lambda/c\ne 0$, so $cu\in L_A$.

**Closed under addition.** Let $u,v\in L_A$, with $\lambda\ne0,\ \mu\ne0$ such that $\lambda u\in K_A$ and $\mu v\in K_A$. Set
$$
s=\min(|\lambda|,|\mu|)>0 .
$$
By solidity (part (a)), since $|s/\lambda|\le1$ we have $s u=(s/\lambda)(\lambda u)\in K_A$, and likewise $s v\in K_A$. Now take $\rho=s/2\ne0$. Then
$$
\rho(u+v)=\tfrac12(su)+\tfrac12(sv)
$$
is a convex combination ($\theta=\tfrac12$) of the two members $su,sv\in K_A$, so by **convexity of $K_A$** (part (a)), $\rho(u+v)\in K_A$. Hence $u+v\in L_A$.

Therefore $L_A$ is closed under addition and scalar multiplication and contains $0$: it is a linear space. $\qquad\checkmark$

### Part (c): $\|u\|_A$ is a well-defined norm on $L_A$

Recall $\displaystyle\|u\|_A=\inf\Big\{\lambda>0:\int A\big(|u|/\lambda\big)\,dx\le 1\Big\}$. Write $\Lambda(u)$ for the set in braces.

**The set $\Lambda(u)$ is an upward ray.** If $\lambda\in\Lambda(u)$ and $\lambda'>\lambda$, then $|u|/\lambda'\le|u|/\lambda$, so by monotonicity of $A$, $\int A(|u|/\lambda')\le\int A(|u|/\lambda)\le1$, i.e. $\lambda'\in\Lambda(u)$. Thus $\Lambda(u)$ is an interval unbounded above.

**Finiteness ($\Lambda(u)\ne\varnothing$, so $\|u\|_A<\infty$).** Let $u\in L_A$ and fix $\rho\ne0$ with $\rho u\in K_A$, i.e. $\int A(|\rho||u|)<\infty$. For every $\lambda\ge 1/|\rho|$ we have $|u|/\lambda\le|\rho||u|$, hence $A(|u|/\lambda)\le A(|\rho||u|)$, an integrable dominating function independent of $\lambda$. As $\lambda\to\infty$, $|u|/\lambda\to0$ pointwise and $A(|u|/\lambda)\to A(0)=0$ by continuity of $A$; by **Dominated Convergence**, $\int A(|u|/\lambda)\to0$. So for $\lambda$ large enough the integral is $\le1$, giving $\Lambda(u)\ne\varnothing$. Hence $\|u\|_A\in[0,\infty)$ is well-defined.

**Attainment ($\Lambda(u)$ is closed).** Suppose $\|u\|_A>0$ and pick $\lambda_n\downarrow\|u\|_A$ with $\lambda_n\in\Lambda(u)$. Then $A(|u|/\lambda_n)\to A(|u|/\|u\|_A)$ pointwise (continuity of $A$), so by **Fatou's lemma**
$$
\int A\big(|u|/\|u\|_A\big)\le\liminf_n\int A(|u|/\lambda_n)\le 1 .
$$
Thus $\|u\|_A\in\Lambda(u)$: the infimum is attained. (This fact is what makes part (d) sharp.)

We now verify the norm axioms.

**(N1) Nonnegativity.** $\|u\|_A\ge0$ as an infimum of positive numbers.

**(N2) Definiteness.** If $u=0$ a.e., then $\int A(|u|/\lambda)=\int A(0)=0\le1$ for every $\lambda>0$, so $\|u\|_A=0$. Conversely, suppose $\|u\|_A=0$ but $u\ne0$ on a set of positive measure: there are $\varepsilon>0$ and a set $E$ with $|E|=\delta>0$ and $|u|\ge\varepsilon$ on $E$. For $\lambda>0$,
$$
\int A(|u|/\lambda)\ge\int_E A(\varepsilon/\lambda)\,dx=\delta\,A(\varepsilon/\lambda)\xrightarrow[\lambda\to0^+]{}\infty
$$
by coercivity of $A$. So no small $\lambda$ lies in $\Lambda(u)$, contradicting $\inf\Lambda(u)=0$ (recall $\Lambda(u)$ is an upward ray, so $\inf=0$ would force arbitrarily small members). Hence $u=0$ a.e.

**(N3) Homogeneity.** For $c\ne0$, substituting $\mu=\lambda/|c|$,
$$
\int A\big(|cu|/\lambda\big)\le1\iff\int A\big(|u|/(\lambda/|c|)\big)\le1\iff \mu\in\Lambda(u).
$$
Thus $\Lambda(cu)=|c|\,\Lambda(u)$ and $\|cu\|_A=|c|\inf\Lambda(u)=|c|\,\|u\|_A$. For $c=0$, $\|0\|_A=0=|0|\,\|u\|_A$.

**(N4) Triangle inequality.** Let $a=\|u\|_A,\ b=\|v\|_A$. If $a=0$ then $u=0$ a.e. and $\|u+v\|_A=\|v\|_A=a+b$; symmetrically if $b=0$. So assume $a,b>0$. By **attainment**, $\int A(|u|/a)\le1$ and $\int A(|v|/b)\le1$. Set $\lambda=a+b$. Pointwise,
$$
\frac{|u+v|}{a+b}\le\frac{|u|+|v|}{a+b}=\frac{a}{a+b}\cdot\frac{|u|}{a}+\frac{b}{a+b}\cdot\frac{|v|}{b},
$$
a convex combination with weights $\tfrac{a}{a+b}+\tfrac{b}{a+b}=1$. Using monotonicity then convexity of $A$,
$$
A\!\left(\frac{|u+v|}{a+b}\right)\le \frac{a}{a+b}\,A\!\left(\frac{|u|}{a}\right)+\frac{b}{a+b}\,A\!\left(\frac{|v|}{b}\right).
$$
Integrating,
$$
\int A\!\left(\frac{|u+v|}{a+b}\right)\le\frac{a}{a+b}\cdot1+\frac{b}{a+b}\cdot1=1 .
$$
Hence $a+b\in\Lambda(u+v)$, so $\|u+v\|_A\le a+b=\|u\|_A+\|v\|_A$.

All axioms hold, so $\|\cdot\|_A$ is a well-defined norm on $L_A$ (the **Luxemburg norm**). $\qquad\checkmark$

### Part (d): the Hölder-type inequality

**Step 1 — Young's inequality.** *For all $s,t\in[0,\infty)$, $\ st\le A(s)+\tilde A(t)$, with equality iff $t=\alpha(s)$.*

Fix $s\ge0$ and consider $\varphi(t)=A(s)+\tilde A(t)-st$ on $[0,\infty)$. Then $\varphi$ is convex (as $\tilde A$ is), with $\varphi(0)=A(s)\ge0$, and right-derivative $\tilde A'(t)-s=\alpha^{-1}(t)-s$, which is $<0$ for $t<\alpha(s)$ and $>0$ for $t>\alpha(s)$ (because $\alpha^{-1}$ is strictly increasing and $\alpha^{-1}(\alpha(s))=s$). So $\varphi$ attains its minimum at $t^\*=\alpha(s)$. There,
$$
\varphi(\alpha(s))=A(s)+\tilde A(\alpha(s))-s\,\alpha(s).
$$
The **complementary identity** $A(s)+\tilde A(\alpha(s))=s\,\alpha(s)$ holds: substituting $\tau=\alpha(\sigma)$ in $\tilde A(\alpha(s))=\int_0^{\alpha(s)}\alpha^{-1}(\tau)\,d\tau$ gives $\int_0^s\sigma\,d\alpha(\sigma)$, and integrating by parts,
$$
\int_0^s\sigma\,d\alpha(\sigma)=\big[\sigma\,\alpha(\sigma)\big]_0^s-\int_0^s\alpha(\sigma)\,d\sigma=s\,\alpha(s)-A(s).
$$
(Equivalently: $A(s)$ is the area under $y=\alpha(x)$ over $[0,s]$, $\tilde A(\alpha(s))$ is the complementary area between that curve and the $y$-axis up to height $\alpha(s)$, and the two together tile the rectangle $[0,s]\times[0,\alpha(s)]$ of area $s\,\alpha(s)$.) Hence $\varphi(\alpha(s))=0$, so $\varphi(t)\ge0$ everywhere, i.e.
$$
st\le A(s)+\tilde A(t),\qquad s,t\ge0,
$$
with equality exactly at $t=\alpha(s)$. $\qquad\checkmark$

**Step 2 — from Young to Hölder.** Let $u\in L_A$, $v\in L_{\tilde A}$, and put $a=\|u\|_A$, $b=\|v\|_{\tilde A}$. If $a=0$ then $u=0$ a.e. and $\int uv=0\le 2ab$; similarly if $b=0$. So assume $a,b>0$. Apply Young's inequality pointwise with $s=|u(x)|/a$ and $t=|v(x)|/b$:
$$
\frac{|u(x)|}{a}\cdot\frac{|v(x)|}{b}\le A\!\left(\frac{|u(x)|}{a}\right)+\tilde A\!\left(\frac{|v(x)|}{b}\right).
$$
Integrate over $[0,1]$ and use the **attainment** from part (c) — $\int A(|u|/a)\le1$ and $\int \tilde A(|v|/b)\le1$:
$$
\frac{1}{ab}\int_0^1|u(x)||v(x)|\,dx\;\le\;\int_0^1 A\!\left(\frac{|u|}{a}\right)dx+\int_0^1\tilde A\!\left(\frac{|v|}{b}\right)dx\;\le\;1+1=2 .
$$
Therefore $\int_0^1|u||v|\,dx\le 2ab=2\|u\|_A\,\|v\|_{\tilde A}$, and since $\int_0^1 u v\,dx\le\int_0^1|u||v|\,dx$,
$$
\int_0^1 u(x)\,v(x)\,dx\le 2\,\|u\|_A\,\|v\|_{\tilde A}. \qquad\blacksquare
$$

### Remark — the structure on display

The four parts assemble, in dependency order, the standard machinery of Orlicz spaces. Convexity of $A$ (from $\alpha$ increasing) drives (a); solidity plus that convexity drive (b); the same convexity, together with the Fatou-attainment of the Luxemburg infimum, drives the triangle inequality in (c); and the complementary pairing of $A$ with $\tilde A$ — Young's inequality — drives the duality in (d). The constant $2$ in Hölder is intrinsic to the **Luxemburg norm**: each function is normalized so that its modular integral is $\le1$, and the two integrals add. (Passing instead to the equivalent **Orlicz norm** $\|v\|^{\mathrm{O}}_{\tilde A}=\sup\{\int uv:\|u\|_A\le1\}$ removes the factor, at the cost of a less explicit definition.) When $\alpha(t)=t^{p-1}$ one recovers $A(t)=t^p/p$, $\tilde A(t)=t^q/q$ with $1/p+1/q=1$, $\|\cdot\|_A\propto\|\cdot\|_{L^p}$, and the inequality is ordinary Hölder.

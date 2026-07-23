<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b03J04: The splitting field of xᵖ − β, and the irreducible-or-has-a-root dichotomy

## Why It's Hard

The polynomial $x^p-\beta$ has two independent ingredients tangled together — a single $p$-th root $\alpha$ of $\beta$, and the $p$-th roots of unity that produce the *other* roots — and the problem asks you to disentangle them without knowing the characteristic of $k$. That last point is a hidden trap: if $\operatorname{char}k\ne p$ then $x^p-1$ is separable with $p$ distinct roots, but if $\operatorname{char}k=p$ then $x^p-1=(x-1)^p$ has the *single* root $1$. A correct argument must work **uniformly** across both regimes.

- **Part (a)** asks you to locate a splitting field $K_1$ of $x^p-1$ *inside* $K$ — but $K$ is defined only as a splitting field of $x^p-\beta$, with no a priori roots of unity in sight. The non-obvious structural fact is that the roots of unity come along **for free**: any ratio of two roots of $x^p-\beta$ is a $p$-th root of unity, so $K$ already contains all of them.
- **Part (b)** asserts a dichotomy — *irreducible or has a root in $k$* — that is false for general polynomials (most are neither). It holds here because of the rigid root structure, and the proof requires converting a hypothetical proper factor into the statement "$\beta$ is a $p$-th power in $k$" via a coprimality/Bézout argument that uses the primality of $p$ essentially.

## The Key Insight

**All roots of $x^p-\beta$ differ by a $p$-th root of unity.** If $\alpha,\gamma$ are roots then $(\gamma/\alpha)^p=\beta/\beta=1$, so $\gamma=\zeta\alpha$ with $\zeta^p=1$. Two consequences:

- **(a)** Every $p$-th root of unity $\zeta$ equals $(\zeta\alpha)/\alpha$, a ratio of two roots of $f$, both in $K$; so $K$ contains *all* roots of $x^p-1$, hence the splitting field $K_1=k(\mu_p)$. And $K=k(\text{roots of }f)=k(\{\zeta\alpha\})=K_1(\alpha)$.
- **(b)** A proper degree-$d$ factor of $f$ has constant term $\pm(\text{product of }d\text{ roots})=\pm\omega\,\alpha^d$ with $\omega^p=1$; this lies in $k$, and raising to the $p$-th power gives $\beta^d\in k^{\times p}$. Since $0<d<p$ and $p$ is prime, $\gcd(d,p)=1$, so **Bézout upgrades "$\beta^d$ is a $p$-th power" to "$\beta$ is a $p$-th power"** — i.e. $f$ has a root in $k$.

## Complete Proof

Let $p$ be prime, $k$ a field, $\beta\in k^\times$, and $K$ a splitting field of $f(x)=x^p-\beta$ over $k$. Fix a root $\alpha\in K$ of $f$ (one exists since $f$ splits in $K$); note $\alpha\ne 0$ because $\alpha^p=\beta\ne 0$.

### Part (a): $K\supseteq K_1$ a splitting field of $x^p-1$, and $K=K_1(\alpha)$

**Roots of $f$ are root-of-unity multiples of $\alpha$.** If $\gamma\in K$ is any root of $f$, then $\gamma^p=\beta=\alpha^p$, so $(\gamma/\alpha)^p=1$ (using $\alpha\ne0$ in the field $K$); thus $\zeta:=\gamma/\alpha$ satisfies $\zeta^p=1$ and $\gamma=\zeta\alpha$. Conversely, if $\zeta^p=1$ then $(\zeta\alpha)^p=\beta$, so $\zeta\alpha$ is a root of $f$. Hence
$$
\{\text{roots of }f\text{ in }K\}=\{\zeta\alpha:\ \zeta\in K,\ \zeta^p=1\}. \tag{1}
$$

**$x^p-1$ splits in $K$.** Let $\zeta_0$ be a root of $x^p-1$ in any extension of $k$. Then $\zeta_0\alpha$ satisfies $(\zeta_0\alpha)^p=\beta$, i.e. $\zeta_0\alpha$ is a root of $f$; since $K$ is a splitting field of $f$, every root of $f$ lies in $K$, so $\zeta_0\alpha\in K$, and therefore $\zeta_0=(\zeta_0\alpha)/\alpha\in K$. Thus **all** roots of $x^p-1$ lie in $K$, so $x^p-1$ splits over $K$. Define
$$
K_1:=k\big(\{\zeta\in K:\zeta^p=1\}\big)\subseteq K,
$$
the subfield generated over $k$ by all $p$-th roots of unity in $K$: this is a splitting field of $x^p-1$ over $k$, and it sits inside $K$.

**$K=K_1(\alpha)$.** By definition $K=k(\text{roots of }f)$, and by $(1)$ the roots are the $\zeta\alpha$. Each such $\zeta\alpha$ lies in $K_1(\alpha)$ (as $\zeta\in K_1$, $\alpha\in K_1(\alpha)$), so $K\subseteq K_1(\alpha)$. Conversely $K_1\subseteq K$ and $\alpha\in K$, so $K_1(\alpha)\subseteq K$. Hence
$$
K=K_1(\alpha). \qquad\checkmark
$$
*(Characteristic check: if $\operatorname{char}k=p$ then the only $p$-th root of unity is $1$, so $K_1=k$ and $K=k(\alpha)$; the argument above is unaffected.)*

### Part (b): $f$ is irreducible over $k$, or has a root in $k$

We prove the contrapositive-friendly statement: **if $f$ is reducible in $k[x]$, then $f$ has a root in $k$.**

Suppose $f=g\,h$ in $k[x]$ with $g,h$ monic (legitimate, dividing out unit leading coefficients) and $d:=\deg g$ satisfying $1\le d<p$. Over $K$, $f$ splits and by $(1)$ its monic factor $g$ is a product of $d$ of the linear factors $(x-\zeta_i\alpha)$:
$$
g(x)=\prod_{i=1}^{d}(x-\zeta_i\alpha),\qquad \zeta_i^p=1.
$$
Comparing constant terms and writing $\omega:=\prod_{i=1}^d\zeta_i$ (so $\omega^p=\prod\zeta_i^p=1$),
$$
g(0)=\prod_{i=1}^d(-\zeta_i\alpha)=(-1)^d\,\omega\,\alpha^{d}.
$$
Since $g\in k[x]$, $g(0)\in k$; set $c:=(-1)^d g(0)=\omega\alpha^{d}\in k$. Note $c\ne 0$ (a product of nonzero elements). Raising to the $p$-th power and using $\omega^p=1$, $\alpha^p=\beta$:
$$
c^{p}=\omega^{p}\,\alpha^{dp}=(\alpha^{p})^{d}=\beta^{d}. \tag{2}
$$
Now $\gcd(d,p)=1$ (as $0<d<p$ and $p$ is prime), so there are integers $u,v$ with $ud+vp=1$. Using $(2)$ and $\beta\in k^\times$,
$$
\beta=\beta^{ud+vp}=(\beta^{d})^{u}(\beta^{p})^{v}=(c^{p})^{u}\beta^{pv}=\big(c^{u}\beta^{v}\big)^{p}.
$$
Set $\delta:=c^{u}\beta^{v}\in k$ (well-defined: $c,\beta\in k^\times$, integer powers make sense in the field $k$). Then $\delta^{p}=\beta$, so $\delta$ is a root in $k$ of $f(x)=x^p-\beta$.

Therefore a reducible $f$ has a root in $k$; equivalently, $f$ is irreducible in $k[x]$ **or** $f$ has a root in $k$. $\qquad\blacksquare$

### Remark — the radical-extension structure and the dichotomy's meaning

Part (a) exhibits the splitting field of a *pure equation* $x^p=\beta$ as a two-step tower
$$
k\ \subseteq\ K_1=k(\mu_p)\ \subseteq\ K=K_1(\alpha),
$$
first adjoin the roots of unity (an abelian "cyclotomic" layer), then adjoin one radical $\alpha=\beta^{1/p}$ (a "Kummer" layer). This is the prototype of radical extensions in Galois theory, underlying the solvability-by-radicals criterion. Part (b) is the **flat dichotomy for binomials $x^p-\beta$, $p$ prime**: there is no intermediate factorization. The slogan is that $\beta$ being a $p$-th power in $k$ is the *only* obstruction to irreducibility — a proper factor would force $\beta^{\gcd(d,p)}=\beta$ to be a $p$-th power. The same Bézout engine appears in b01A01(a) (the special case $k$ of characteristic $p$, $\beta=a$); here it is exposed in full generality, valid in every characteristic. (Caveat for completeness: the clean "$p$ prime" dichotomy genuinely uses primality — for composite exponents $x^n-\beta$ can factor without having a root, e.g. $x^4+4=(x^2-2x+2)(x^2+2x+2)$ over $\mathbb{Q}$.)

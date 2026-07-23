<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b01A01: x^p − a splits or is irreducible, and perfect fields have only separable irreducibles

## Why It's Hard

Both parts are characteristic-$p$ rigidity phenomena that have **no characteristic-zero analogue**, and the proofs hinge on the same engine — the Frobenius map and the "freshman's dream" $(u+v)^p=u^p+v^p$ — used in two different guises.

- **Part (a)** asserts a *dichotomy* that would be bizarre in general: most polynomials are neither split nor irreducible (e.g. $x^4-5x^2+6$ over $\mathbb{Q}$ is a product of two irreducible quadratics). That $x^p-a$ can *only* split completely or be irreducible — never partially factor — is special. The reason is that in characteristic $p$ the polynomial has a **single root of multiplicity $p$**: $x^p-a=(x-\alpha)^p$. So every monic factor is a power $(x-\alpha)^d$, and the difficulty is the number-theoretic step showing that the existence of a *proper* such factor forces $\alpha$ itself into $k$ — via the coprimality $\gcd(d,p)=1$ and Bézout.

- **Part (b)** must convert a hypothesis about *elements* (Frobenius is surjective: every element has a $p$-th root) into a statement about *polynomials* (irreducibles have no repeated roots). The non-obvious bridge is that surjectivity of Frobenius is precisely what lets you extract a $p$-th root of an *entire polynomial*. The chain "inseparable irreducible $\Rightarrow f'=0\Rightarrow f\in k[x^p]\Rightarrow f=h^p\Rightarrow$ reducible" is the only route, and each arrow needs a separate characteristic-$p$ fact.

## The Key Insight

In characteristic $p$, **Frobenius turns $x^p-a$ into a perfect $p$-th power**: if $\alpha^p=a$ then $x^p-a=x^p-\alpha^p=(x-\alpha)^p$. The whole problem flows from this and its polynomial-level version.

- **(a)** The factor structure of $(x-\alpha)^p$ is just the ladder $(x-\alpha)^d$, $0\le d\le p$. A proper monic factor in $k[x]$ has $0<d<p$, hence $\gcd(d,p)=1$; Bézout then writes $\alpha=(\alpha^d)^u(\alpha^p)^v\in k$, so $a=\alpha^p$ already had a $p$-th root in $k$ — the *split* case. No proper factor $\Rightarrow$ irreducible. Dichotomy.

- **(b)** An inseparable irreducible has $f'=0$, so $f$ is a polynomial in $x^p$: $f=\sum c_i x^{pi}$. Surjective Frobenius supplies $b_i$ with $b_i^p=c_i$, and freshman's dream collapses $f=\sum b_i^p x^{pi}=\big(\sum b_i x^i\big)^p=h^p$ — a proper power, contradicting irreducibility.

Both parts: *being a $p$-th power is detected and exploited through Frobenius.*

## Complete Proof

Let $k$ be a field with $\operatorname{char}k=p>0$. Recall the **Frobenius homomorphism** $\sigma(\alpha)=\alpha^p$ is a ring endomorphism of $k$ (and of $k[x]$), because $(u+v)^p=u^p+v^p$ in characteristic $p$ (all middle binomial coefficients $\binom{p}{j}$, $0<j<p$, are divisible by $p$).

### Part (a): $x^p-a$ splits in $k[x]$ or is irreducible

Work in a splitting field $\bar k\supseteq k$ of $f(x)=x^p-a$, and let $\alpha\in\bar k$ be a root, so $\alpha^p=a$. Then, in $\bar k[x]$,
$$
f(x)=x^p-a=x^p-\alpha^p=(x-\alpha)^p. \tag{1}
$$

**Case 1: $a$ has a $p$-th root in $k$.** If $\alpha\in k$, then $(1)$ already holds in $k[x]$ and $f$ splits completely in $k[x]$.

**Case 2: $a$ has no $p$-th root in $k$ (i.e. $\alpha\notin k$).** Suppose, for contradiction, $f$ is reducible in $k[x]$: then it has a monic factor $g\in k[x]$ with $0<\deg g=d<p$. By $(1)$ and unique factorization in $\bar k[x]$, the only monic divisors of $(x-\alpha)^p$ are the powers $(x-\alpha)^j$; hence
$$
g(x)=(x-\alpha)^d .
$$
Its constant term is $(-\alpha)^d=(-1)^d\alpha^d$, and since $g\in k[x]$, this lies in $k$; thus $\alpha^d\in k$. Now $0<d<p$ with $p$ prime gives $\gcd(d,p)=1$, so by Bézout there are integers $u,v$ with $ud+vp=1$. Then
$$
\alpha=\alpha^{ud+vp}=(\alpha^d)^u\,(\alpha^p)^v=(\alpha^d)^u\,a^v\in k,
$$
since $\alpha^d\in k$ and $a\in k$. But $\alpha\in k$ means $a=\alpha^p$ has a $p$-th root in $k$, contradicting Case 2. Hence $f$ has no proper factor and is **irreducible** in $k[x]$.

In either case, $f$ splits or is irreducible. $\qquad\checkmark$

### Part (b): if Frobenius is surjective, every irreducible polynomial is separable

Recall a non-constant polynomial is **separable** iff it has no repeated root in a splitting field, and that for an **irreducible** $f$ this is equivalent to $f'\ne 0$: indeed $\gcd(f,f')$ is a divisor of the irreducible $f$, so it is $1$ or (an associate of) $f$; since $\deg f'<\deg f$, it equals $f$ only when $f'=0$, and $\gcd(f,f')=f$ is exactly the presence of a repeated root. So it suffices to show: **no irreducible polynomial has $f'=0$.**

Suppose, for contradiction, that $f\in k[x]$ is irreducible (so $\deg f\ge 1$) with $f'=0$. Writing $f=\sum_{j} c_j x^{j}$, the derivative $f'=\sum_j j\,c_j x^{j-1}$ vanishes iff $j\,c_j=0$ for all $j$, i.e. $c_j=0$ whenever $p\nmid j$. Thus only exponents divisible by $p$ occur:
$$
f(x)=\sum_{i} c_{pi}\,x^{pi},\qquad\text{i.e. } f\in k[x^p].
$$
Now use surjectivity of Frobenius: each coefficient $c_{pi}\in k$ has a $p$-th root $b_i\in k$ with $b_i^p=c_{pi}$. Applying freshman's dream in $k[x]$,
$$
f(x)=\sum_i c_{pi}\,x^{pi}=\sum_i b_i^{\,p}\,(x^{i})^{p}=\Big(\sum_i b_i\,x^{i}\Big)^{p}=h(x)^p,\qquad h:=\sum_i b_i x^i\in k[x].
$$
Since $\deg f=p\cdot\deg h\ge 1$ and $p\ge 2$, we have $\deg h\ge 1$, so $f=h^p$ exhibits $h$ as a factor of $f$ with $1\le\deg h<\deg f$ — contradicting irreducibility of $f$.

Therefore every irreducible polynomial has $f'\ne 0$ and is separable. $\qquad\blacksquare$

### Remark — perfection and the role of surjectivity

A field of characteristic $p$ is **perfect** exactly when its Frobenius is surjective (every element is a $p$-th power); finite fields and algebraically closed fields are perfect. Part (b) is the statement that *perfect fields have no inseparable irreducible polynomials* — equivalently, every algebraic extension of a perfect field is separable. Surjectivity is essential and sharp: over the imperfect field $k=\mathbb{F}_p(t)$, the element $t$ has **no** $p$-th root, and $x^p-t$ is irreducible (by part (a)!) yet inseparable, since $x^p-t=(x-t^{1/p})^p$ has a single root of multiplicity $p$. So part (a) manufactures the very counterexample that shows part (b)'s hypothesis cannot be dropped — the two parts are two faces of how $p$-th powers control factorization and separability in characteristic $p$.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b97A02: The affine group on F_q(x), its fixed field (xq−x)^{q−1}, and finiteness over subfields

## Why It's Hard

This builds the full picture of the affine group $AGL_1(F_q)$ acting on the rational function field $F_q(x)$, and the steep step is **part (c): explicitly identifying the fixed field**. There is no formula handed to you; you must *discover* the invariant $(x^q-x)^{q-1}$. The obstacle is that the group $G$ has $q(q-1)$ elements mixing translations $x\mapsto x+b$ and scalings $x\mapsto ax$, and an invariant must be unmoved by *all* of them at once. The trick is to first find a **semi-invariant** — an element that every $\sigma_{a,b}$ merely *scales* — and then kill the scaling. The natural candidate $x^q-x=\prod_{c\in F_q}(x-c)$ works precisely because the finite-field identities $a^q=a$, $b^q=b$ make it transform by the clean rule $\sigma_{a,b}(x^q-x)=a(x^q-x)$.

The other parts have their own subtleties: (a)–(b) require knowing that an $F_q$-automorphism of $F_q(x)$ is determined by the image of $x$ and that the composition law is a semidirect product; (c) and (d) both lean on the **degree formula** $[F(x):F(t)]=\max(\deg f,\deg g)$ for $t=f/g$ — the engine that converts "$\theta$ has degree $q(q-1)$" into "$F_q(\theta)$ is the whole fixed field" via Artin's theorem, and that makes $F_q(x)$ finite over *any* non-constant subfield.

## The Key Insight

The polynomial $x^q-x=\prod_{c\in F_q}(x-c)$ is the **affine semi-invariant**: for every $\sigma_{a,b}\in G$,
$$
\sigma_{a,b}(x^q-x)=(ax+b)^q-(ax+b)=a^qx^q+b^q-ax-b=a(x^q-x),
$$
using $a^q=a$ and $b^q=b$ in $F_q$. So $x^q-x$ is a common "eigenvector" with eigenvalue $a\in F_q^\times$. Since $|F_q^\times|=q-1$, raising to that power kills the eigenvalue:
$$
\theta:=(x^q-x)^{q-1}\ \Rightarrow\ \sigma_{a,b}(\theta)=a^{q-1}\theta=\theta,
$$
a genuine $G$-invariant. Artin's theorem gives $[F_q(x):F_q(x)^G]=|G|=q(q-1)$, and the degree formula gives $[F_q(x):F_q(\theta)]=\deg\theta=q(q-1)$; as $F_q(\theta)\subseteq F_q(x)^G$ with equal index, the fixed field is exactly $F_q(\theta)$. Part (d) is the same degree formula in disguise: any non-constant $t$ already makes $F_q(x)$ finite over $F_q(t)$.

## Complete Proof

Write $E=F_q(x)$. Recall the **degree formula**: for $t=f(x)/g(x)\in E\setminus F_q$ with $\gcd(f,g)=1$, the element $x$ is algebraic over $F_q(t)$ with $[E:F_q(t)]=\max(\deg f,\deg g)$ (its minimal polynomial is a scalar multiple of $f(T)-t\,g(T)\in F_q(t)[T]$).

### Part (a): existence and uniqueness of $\sigma_{a,b}$

**Existence.** Since $F_q[x]$ is the free commutative $F_q$-algebra on $x$, sending $x\mapsto ax+b$ extends uniquely to an $F_q$-algebra homomorphism $F_q[x]\to E$, $f(x)\mapsto f(ax+b)$. As $a\ne 0$ this is degree-preserving, hence injective, so it extends to the fraction field by $f/g\mapsto f(ax+b)/g(ax+b)$, giving an $F_q$-algebra endomorphism $\sigma_{a,b}$ of $E$ with $\sigma_{a,b}(x)=ax+b$ and $\sigma_{a,b}|_{F_q}=\mathrm{id}$. It is an automorphism because it has a two-sided inverse: a direct check gives $\sigma_{a^{-1},-a^{-1}b}\circ\sigma_{a,b}=\mathrm{id}$ (see part b).

**Uniqueness.** Any $F_q$-automorphism $\tau$ of $E$ is determined by $\tau(x)$, since $E$ is generated over $F_q$ by $x$ (two $F_q$-homomorphisms agreeing on $x$ agree on $F_q[x]$, hence on $E$). So $\sigma_{a,b}$ is the unique such map. $\qquad\checkmark$

### Part (b): $G$ is a group of order $q(q-1)$

**Composition law.** For $\sigma_{a,b},\sigma_{a',b'}\in G$,
$$
(\sigma_{a',b'}\circ\sigma_{a,b})(x)=\sigma_{a',b'}(ax+b)=a\,\sigma_{a',b'}(x)+b=a(a'x+b')+b=(aa')x+(ab'+b),
$$
so $\sigma_{a',b'}\circ\sigma_{a,b}=\sigma_{aa',\,ab'+b}$, again in $G$ (as $aa'\ne 0$). The identity is $\sigma_{1,0}$, and $\sigma_{a,b}^{-1}=\sigma_{a^{-1},-a^{-1}b}\in G$; associativity is automatic for function composition. So $G$ is a group (the affine group $AGL_1(F_q)\cong F_q\rtimes F_q^\times$).

**Order.** The pair $(a,b)$ is recovered from $\sigma_{a,b}(x)=ax+b$, so distinct pairs give distinct elements; with $a\in F_q^\times$ ($q-1$ choices) and $b\in F_q$ ($q$ choices),
$$
|G|=q(q-1). \qquad\checkmark
$$

### Part (c): the fixed field is $F_q\big((x^q-x)^{q-1}\big)$

**$\theta:=(x^q-x)^{q-1}$ is $G$-invariant.** As computed in the Key Insight, $\sigma_{a,b}(x^q-x)=a(x^q-x)$ for every $\sigma_{a,b}\in G$ (using $a^q=a,\ b^q=b$). Hence
$$
\sigma_{a,b}(\theta)=\big(\sigma_{a,b}(x^q-x)\big)^{q-1}=(a(x^q-x))^{q-1}=a^{q-1}\theta=\theta,
$$
since $a^{q-1}=1$ for $a\in F_q^\times$. Thus $\theta\in E^G$ and $F_q(\theta)\subseteq E^G$.

**Degree count forces equality.** By **Artin's theorem**, $G$ is a finite automorphism group of $E$, $E/E^G$ is Galois with group $G$, and
$$
[E:E^G]=|G|=q(q-1).
$$
On the other hand, $\theta=(x^q-x)^{q-1}$ is a polynomial in $x$ of degree $q\cdot(q-1)=q(q-1)$ (leading term $x^{q(q-1)}$), so by the degree formula (numerator degree $q(q-1)$, denominator $1$),
$$
[E:F_q(\theta)]=q(q-1).
$$
From $F_q(\theta)\subseteq E^G\subseteq E$ and $[E:F_q(\theta)]=q(q-1)=[E:E^G]$, we get $[E^G:F_q(\theta)]=1$, i.e.
$$
E^G=F_q(\theta)=F_q\big((x^q-x)^{q-1}\big). \qquad\checkmark
$$

### Part (d): $F_q(x)$ is finite over any subfield $K\supsetneq F_q$

Since $K$ properly contains $F_q$, choose $t\in K\setminus F_q$; then $t$ is non-constant. By the degree formula, $x$ is algebraic over $F_q(t)$ and
$$
[E:F_q(t)]=\max(\deg f,\deg g)<\infty,\qquad t=f/g\ (\gcd(f,g)=1).
$$
(Concretely, $x$ is a root of the nonzero polynomial $f(T)-t\,g(T)\in F_q(t)[T]$, nonzero because $t\notin F_q$.) Now $F_q(t)\subseteq K\subseteq E$, so by multiplicativity of degrees
$$
[E:K]\ \le\ [E:K]\,[K:F_q(t)]=[E:F_q(t)]<\infty .
$$
Hence $F_q(x)=E$ is finite over $K$. $\qquad\blacksquare$

### Remark — semi-invariants, Artin, and Lüroth

The heart of the problem is the **semi-invariant trick**: under a group acting by automorphisms, first find an element scaled by a character ($x^q-x\mapsto a\,(x^q-x)$, character $\sigma_{a,b}\mapsto a$ into $F_q^\times$), then raise to the order of the character group ($q-1$) to land in the kernel and obtain a true invariant. This is the same character-killing idea behind Kummer theory and $F$-purity (cf. b95J04, b96A03). Artin's theorem supplies the exact degree $|G|$, and the degree formula supplies the matching degree for the candidate generator — so the two numbers pinch the fixed field to $F_q((x^q-x)^{q-1})$. Part (d) is a facet of **Lüroth's theorem**: every subfield of $F_q(x)$ strictly above $F_q$ is itself a rational function field $F_q(s)$ over which $F_q(x)$ is finite; we proved the finiteness directly, which is all that is needed. Geometrically, $G$ realizes $F_q(x)^G\hookrightarrow F_q(x)$ as the degree-$q(q-1)$ cover of the projective line by itself given by the affine group — and $(x^q-x)^{q-1}$ is the defining invariant coordinate downstairs.

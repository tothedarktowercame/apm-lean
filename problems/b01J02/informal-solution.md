<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b01J02: The ideal structure of ℤ[x] — maximal ideals, a non-prime ideal, and dimension 2

## Why It's Hard

The whole problem is a stress test of the fact that **$\mathbb{Z}[x]$ has Krull dimension $2$** — it is neither a PID nor a polynomial ring over a field, and its ideal theory is strictly richer than either $\mathbb{Z}$ (maximal ideals $(p)$) or $k[x]$ (maximal ideals $(f)$, $f$ irreducible). Students fluent in those two one-dimensional cases must *combine* them, and the new phenomena are exactly where the difficulty lives:

- **(a)** Maximal ideals need **two** generators, a prime $p$ *and* a polynomial — a hallmark of dimension $2$. Proving that *every* maximal ideal has this shape requires the genuinely subtle step of ruling out $M\cap\mathbb{Z}=(0)$, i.e. showing the residue field has positive characteristic. That needs Nullstellensatz-type input (a field finitely generated as a $\mathbb{Z}$-algebra is finite), not just elementary manipulation.
- **(b)** One must spot the *right* factorization. The complex factorization of $x^2+x+1$ (cube roots of unity) is a red herring; the correct lens is **reduction mod $3$**, where $3$ is the "ramified" prime and $x^2+x+1$ becomes a perfect square. Finding that square is the crux.
- **(c)** Tests whether you truly believe dimension is $2$: nonzero primes that fail to be maximal exist *precisely* because there are proper chains $0\subsetneq(p)\subsetneq(p,f)$ of primes.

## The Key Insight

The prime spectrum of $\mathbb{Z}[x]$ has **three layers**, and naming them answers all three parts at once:

| height | prime ideals | quotient | role |
|---|---|---|---|
| $0$ | $(0)$ | $\mathbb{Z}[x]$ | the generic point |
| $1$ | $(p)$ or $(f)$, $f$ irreducible primitive | $\mathbb{F}_p[x]$ or $\mathbb{Z}[\theta]$ — a **domain, not a field** | nonzero prime, **not maximal** |
| $2$ | $(p,\,f)$, $f$ irreducible mod $p$ | finite field $\mathbb{F}_{p^{\deg \bar f}}$ | **maximal** |

So **maximal $\iff$ two generators** (a prime number and a mod-$p$-irreducible polynomial), while **nonzero-prime-but-not-maximal $\iff$ one generator**. Part (b)'s ideal $(3,x^2+x+1)$ fails to be prime for a different reason entirely: $x^2+x+1\equiv(x-1)^2\pmod 3$ is a *square*, so the quotient $\mathbb{F}_3[x]/((x-1)^2)$ has a nonzero nilpotent and is not even a domain.

## Complete Proof

### Part (a): all maximal ideals of $\mathbb{Z}[x]$

**Claim.** The maximal ideals of $\mathbb{Z}[x]$ are exactly
$$
M=(p,\ f(x)),\qquad p\ \text{a prime number},\ \ f(x)\in\mathbb{Z}[x]\ \text{with}\ \bar f\in\mathbb{F}_p[x]\ \text{irreducible},
$$
where $\bar f$ is the reduction of $f$ mod $p$. Their residue fields are the finite fields $\mathbb{Z}[x]/M\cong\mathbb{F}_p[x]/(\bar f)\cong\mathbb{F}_{p^{\deg\bar f}}$.

**These are maximal.** By the third isomorphism theorem,
$$
\mathbb{Z}[x]/(p,f)\cong\big(\mathbb{Z}[x]/(p)\big)\big/(\bar f)=\mathbb{F}_p[x]/(\bar f).
$$
Since $\mathbb{F}_p[x]$ is a PID, $(\bar f)$ is maximal iff $\bar f$ is irreducible, in which case the quotient is a field (indeed the finite field $\mathbb{F}_{p^{\deg\bar f}}$). A quotient being a field means the ideal is maximal.

**Every maximal ideal has this form.** Let $M$ be maximal, so $F:=\mathbb{Z}[x]/M$ is a field. The contraction $\mathfrak p:=M\cap\mathbb{Z}$ is a prime ideal of $\mathbb{Z}$ (preimage of a prime under the inclusion $\mathbb{Z}\hookrightarrow\mathbb{Z}[x]$), so $\mathfrak p=(0)$ or $\mathfrak p=(p)$.

*The case $\mathfrak p=(0)$ is impossible:* $F$ is generated as a ring by $\mathbb{Z}$ and the image of $x$, i.e. $F$ is a **finitely generated $\mathbb{Z}$-algebra that is a field**. By Zariski's lemma (the general/over-$\mathbb{Z}$ form of the Nullstellensatz), such a field is **finite**; a finite field has positive characteristic, forcing $\mathbb{Z}\to F$ to have nontrivial kernel, i.e. $\mathfrak p\ne(0)$.

Hence $\mathfrak p=(p)$ for some prime $p$, so $M\supseteq(p)$ and $M/(p)$ is a maximal ideal of $\mathbb{Z}[x]/(p)=\mathbb{F}_p[x]$. As $\mathbb{F}_p[x]$ is a PID, $M/(p)=(\bar f)$ for some irreducible $\bar f$; lifting $\bar f$ to $f\in\mathbb{Z}[x]$ gives $M=(p,f)$ with $\bar f$ irreducible. $\qquad\checkmark$

### Part (b): $(3,\,x^2+x+1)$ is not prime

Work modulo $3$. Since $-2\equiv 1\pmod 3$,
$$
(x-1)^2=x^2-2x+1\equiv x^2+x+1 \pmod 3 .
$$
Take $f(x)=g(x)=x-1$. Then
$$
f(x)g(x)=(x-1)^2=(x^2+x+1)-3x\in(3,\ x^2+x+1),
$$
so the product lies in $I:=(3,x^2+x+1)$.

But $x-1\notin I$. Indeed $\mathbb{Z}[x]/I\cong\mathbb{F}_3[x]/(\overline{x^2+x+1})=\mathbb{F}_3[x]/\big((x-1)^2\big)$, and the image of $x-1$ there is nonzero: if $x-1\in I$ then reducing mod $3$ would give $(x-1)^2\mid (x-1)$ in $\mathbb{F}_3[x]$, impossible by comparing degrees. Hence
$$
f g=(x-1)^2\in I,\qquad f=g=x-1\notin I,
$$
so $I$ is **not prime**. $\qquad\checkmark$

*(Conceptually: $\mathbb{Z}[x]/I\cong\mathbb{F}_3[x]/((x-1)^2)$ has the nonzero nilpotent $\overline{x-1}$, so it is not a domain — failing primality. The prime $3$ is exactly where $x^2+x+1$ has a repeated root, i.e. where its discriminant $1-4=-3$ vanishes.)*

### Part (c): not every nonzero prime ideal is maximal

**No.** The ideal $(x)$ is a nonzero prime that is not maximal.

- *$(x)$ is prime:* the evaluation map $\mathbb{Z}[x]\to\mathbb{Z}$, $h\mapsto h(0)$, is a surjective ring homomorphism with kernel $(x)$, so $\mathbb{Z}[x]/(x)\cong\mathbb{Z}$, an integral domain. A quotient by $(x)$ being a domain means $(x)$ is prime. And $(x)\ne(0)$.
- *$(x)$ is not maximal:* $\mathbb{Z}$ is not a field, equivalently $(x)$ is properly contained in a larger proper ideal:
$$
(x)\subsetneq(2,\ x)\subsetneq\mathbb{Z}[x],
$$
where $(2,x)$ is proper since $\mathbb{Z}[x]/(2,x)\cong\mathbb{F}_2\ne 0$ (in fact $(2,x)$ is maximal, a part-(a) ideal with $p=2$, $f=x$).

So $(x)$ is a nonzero prime ideal that is not maximal. $\qquad\blacksquare$

*(Other valid examples: $(p)$ for any prime $p$, with $\mathbb{Z}[x]/(p)=\mathbb{F}_p[x]$ a domain but not a field and $(p)\subsetneq(p,x)$; or $(x^2+1)$, with $\mathbb{Z}[x]/(x^2+1)\cong\mathbb{Z}[i]$ a domain but not a field. Each is a height-$1$ prime sitting strictly below a maximal ideal.)*

### Remark — the unifying dimension-2 picture

All three parts are facets of $\dim\mathbb{Z}[x]=2$. The maximal ideals (height $2$) are the "closed points," cut out by *two* conditions — choose a prime $p$ (a point of $\operatorname{Spec}\mathbb{Z}$) and then an irreducible polynomial over the residue field $\mathbb{F}_p$; their residue fields are finite. The height-$1$ primes — the $(p)$ (vertical, "fibers over $p$") and the $(f)$ for $f$ irreducible (horizontal, "graphs of algebraic numbers") — are nonzero but not maximal, which is the content of part (c). Part (b) is orthogonal to the height stratification: $(3,x^2+x+1)$ is a height-$2$ ideal that fails to be prime because $x^2+x+1$ is *inseparable/ramified at $3$* (a repeated factor mod $3$), so its quotient carries nilpotents. The lesson is that in $\mathbb{Z}[x]$ "prime number" and "irreducible polynomial" are two independent axes, and ideals must be read along both.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b01A04: Realizing ℤ/3 and ℤ/3 × ℤ/3 as Galois groups over ℚ

## Why It's Hard

The naive reflex — "for a degree-$3$ Galois group, adjoin a cube root" — is **wrong**. The field $\mathbb{Q}(\sqrt[3]{2})$ is *not* Galois over $\mathbb{Q}$: it contains only one of the three roots of $x^3-2$, its Galois closure has group $S_3$, and the cubic field itself is not even normal. A genuine cyclic cubic extension of $\mathbb{Q}$ must be **totally real with square discriminant**, and producing one out of thin air is not obvious. The right idea is structural: **cyclotomic fields are the universal source of abelian extensions of $\mathbb{Q}$** (Kronecker–Weber), and $\mathrm{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q})\cong(\mathbb{Z}/n)^\times$ is fully understood — so one *carves* the desired cyclic group out as a subfield via the Galois correspondence.

Part (b) adds a second obstacle that traps the unwary: **you cannot get $(\mathbb{Z}/3)^2$ from a single prime-power cyclotomic field**, because $(\mathbb{Z}/p)^\times$ is *cyclic* and cyclic groups have only cyclic quotients — there is no non-cyclic $(\mathbb{Z}/3)^2$ quotient. The resolution is to take a **compositum of two independent cyclic cubic fields** and prove the Galois group of the compositum is the *direct product* — which in turn requires verifying the two fields are linearly disjoint (slickest via *distinct ramification*).

## The Key Insight

For a prime $p\equiv 1\pmod 3$, the group $\mathrm{Gal}(\mathbb{Q}(\zeta_p)/\mathbb{Q})\cong(\mathbb{Z}/p)^\times\cong\mathbb{Z}/(p-1)$ is cyclic of order divisible by $3$, so it has a unique subgroup of index $3$; the corresponding fixed field is a **cyclic cubic field** $K\subset\mathbb{Q}(\zeta_p)$, automatically Galois over $\mathbb{Q}$ (subfields of abelian extensions are Galois) with $\mathrm{Gal}(K/\mathbb{Q})\cong\mathbb{Z}/3$.

- **(a)** Take $p=7$: the cubic subfield of $\mathbb{Q}(\zeta_7)$ is $\mathbb{Q}(2\cos\tfrac{2\pi}{7})$, root of $x^3+x^2-2x-1$.
- **(b)** Take two *different* primes, $p=7$ and (say) the prime $3$ via $\mathbb{Q}(\zeta_9)$, giving cyclic cubics $K_1,K_2$ ramified at $7$ and $3$ respectively. Distinct ramification forces $K_1\cap K_2=\mathbb{Q}$, so
$$
\mathrm{Gal}(K_1K_2/\mathbb{Q})\cong\mathrm{Gal}(K_1/\mathbb{Q})\times\mathrm{Gal}(K_2/\mathbb{Q})\cong\mathbb{Z}/3\times\mathbb{Z}/3 .
$$

## Complete Proof

### Part (a): a $\mathbb{Z}/3$-extension

Let $\zeta_7=e^{2\pi i/7}$. Then $\mathbb{Q}(\zeta_7)/\mathbb{Q}$ is Galois with
$$
\mathrm{Gal}(\mathbb{Q}(\zeta_7)/\mathbb{Q})\cong(\mathbb{Z}/7\mathbb{Z})^\times\cong\mathbb{Z}/6\mathbb{Z},
$$
cyclic of order $6$. The cyclic group $\mathbb{Z}/6$ has a unique subgroup $H$ of order $2$; by the Galois correspondence its fixed field $K:=\mathbb{Q}(\zeta_7)^{H}$ has degree $[\mathbb{Q}(\zeta_7):\mathbb{Q}]/|H|=6/2=3$ over $\mathbb{Q}$. Since $\mathbb{Z}/6$ is abelian, $H$ is normal, so $K/\mathbb{Q}$ is Galois with
$$
\mathrm{Gal}(K/\mathbb{Q})\cong(\mathbb{Z}/6)/(\mathbb{Z}/2)\cong\mathbb{Z}/3 .
$$

**Concretely**, $H=\{1,\text{complex conjugation}\}$, so $K$ is the maximal real subfield $K=\mathbb{Q}(\zeta_7+\zeta_7^{-1})=\mathbb{Q}\big(2\cos\tfrac{2\pi}{7}\big)$. Setting $\alpha=\zeta_7+\zeta_7^{-1}$, the three conjugates $\zeta_7^k+\zeta_7^{-k}$ ($k=1,2,3$) have elementary symmetric sums $e_1=\sum_{j=1}^6\zeta_7^{\,j}=-1$, $e_2=-2$, $e_3=1$, so $\alpha$ is a root of
$$
m(x)=x^3+x^2-2x-1 .
$$
This is irreducible over $\mathbb{Q}$ (no rational root: $m(\pm1)\ne 0$), and its discriminant is
$$
\Delta=18abc-4a^3c+a^2b^2-4b^3-27c^2\big|_{(a,b,c)=(1,-2,-1)}=36+4+4+32-27=49=7^2,
$$
a perfect square. An irreducible cubic with square discriminant has Galois group contained in $A_3$, hence equal to $A_3\cong\mathbb{Z}/3$. So
$$
\boxed{\,K=\mathbb{Q}\big(2\cos\tfrac{2\pi}{7}\big),\quad \mathrm{Gal}(K/\mathbb{Q})\cong\mathbb{Z}/3\mathbb{Z}.\,}
$$

### Part (b): a $\mathbb{Z}/3\times\mathbb{Z}/3$-extension

We exhibit two independent cyclic cubic fields and take their compositum.

**Two cyclic cubics.** From part (a), $K_1=\mathbb{Q}(2\cos\tfrac{2\pi}{7})$ is cyclic cubic over $\mathbb{Q}$. For the second, use $\zeta_9=e^{2\pi i/9}$: $\mathrm{Gal}(\mathbb{Q}(\zeta_9)/\mathbb{Q})\cong(\mathbb{Z}/9)^\times\cong\mathbb{Z}/6$, and exactly as above its cubic subfield is $K_2=\mathbb{Q}(2\cos\tfrac{2\pi}{9})$. Here $\beta=2\cos\tfrac{2\pi}{9}$ satisfies (from $\cos 3\theta=4\cos^3\theta-3\cos\theta$ with $3\theta=\tfrac{2\pi}{3}$, $\cos\tfrac{2\pi}{3}=-\tfrac12$):
$$
\beta^3-3\beta+1=0,
$$
irreducible with discriminant $\Delta=-4(-3)^3-27(1)^2=108-27=81=9^2$, again a perfect square, so $\mathrm{Gal}(K_2/\mathbb{Q})\cong\mathbb{Z}/3$.

**Linear disjointness via ramification.** $K_1\subset\mathbb{Q}(\zeta_7)$ is ramified only at the prime $7$, while $K_2\subset\mathbb{Q}(\zeta_9)$ is ramified only at $3$. The intersection $K_1\cap K_2$ is a subfield of each, Galois over $\mathbb{Q}$, of degree dividing $\gcd(3,3)=3$. If $[K_1\cap K_2:\mathbb{Q}]=3$ then $K_1\cap K_2=K_1=K_2$, forcing a field ramified at both $7$ and $3$ to equal one ramified at only one of them — impossible. Hence
$$
K_1\cap K_2=\mathbb{Q}.
$$

**The compositum.** Let $L=K_1K_2=\mathbb{Q}\big(2\cos\tfrac{2\pi}{7},\,2\cos\tfrac{2\pi}{9}\big)$. By the standard theorem on composita of Galois extensions: *if $K_1,K_2/\mathbb{Q}$ are Galois with $K_1\cap K_2=\mathbb{Q}$, then $K_1K_2/\mathbb{Q}$ is Galois and the restriction map*
$$
\mathrm{Gal}(K_1K_2/\mathbb{Q})\;\xrightarrow{\ \sim\ }\;\mathrm{Gal}(K_1/\mathbb{Q})\times\mathrm{Gal}(K_2/\mathbb{Q}),\qquad \sigma\mapsto(\sigma|_{K_1},\sigma|_{K_2}),
$$
*is an isomorphism.* (It is an injective homomorphism because an automorphism trivial on both $K_1$ and $K_2$ is trivial on their compositum; it is surjective because $K_1\cap K_2=\mathbb{Q}$ makes the orders match, $[L:\mathbb{Q}]=[K_1:\mathbb{Q}][K_2:\mathbb{Q}]=9$.) Therefore
$$
\boxed{\,\mathrm{Gal}(L/\mathbb{Q})\cong\mathbb{Z}/3\mathbb{Z}\times\mathbb{Z}/3\mathbb{Z},\qquad [L:\mathbb{Q}]=9.\,}\qquad\blacksquare
$$

### Remark — why cyclotomic fields, and the general recipe

By the **Kronecker–Weber theorem**, every abelian extension of $\mathbb{Q}$ lies inside some cyclotomic field, so $\mathbb{Q}(\zeta_n)$ and its subfields realize *exactly* the finite abelian groups as Galois groups over $\mathbb{Q}$. The recipe is: to realize $\prod_i \mathbb{Z}/m_i$, pick distinct primes $p_i\equiv 1\pmod{m_i}$, take the index-correct cyclic subfield $K_i\subset\mathbb{Q}(\zeta_{p_i})$ of degree $m_i$, and form the compositum — distinct ramification guarantees pairwise (indeed mutual) linear disjointness, and the compositum's Galois group is the direct product. The single-prime obstruction in part (b) — a cyclic group cannot surject onto $(\mathbb{Z}/3)^2$ — is exactly why $(\mathbb{Z}/3)^2$ needs *two* primes, and is the abelian-group-theory shadow of the fact that $\mathrm{Gal}(\mathbb{Q}(\zeta_p)/\mathbb{Q})$ is always cyclic.

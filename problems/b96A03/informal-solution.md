<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b96A03: F-pure group actions and the descent of primes to the invariant ring

## Why It's Hard

This is a self-contained theory culminating in a genuine theorem: when a finite group $G$ acting on $R=F[x_1,\dots,x_n]$ is **$F$-pure**, the primes of $R$ produce primes of the invariant ring $R^G$ via the **orbit-product** $G(\pi)=\prod_{\text{orbit}}g(\pi)$. The difficulty is that the abstract hypothesis "$F$-pure" (no subgroup of $G$ has a nontrivial homomorphism to $F^*$) has to be *converted into usable ring theory*, and the conversion happens at exactly one step — part (c) — which everything downstream depends on.

- **(a)** tests whether you see that $F$-purity is about *torsion in $F^*$*: an odd-order group can only map to the roots of unity of $F^*$, and $\mathbb{Q}^*$ has only $\pm1$.
- **(c)** is the crux: the units $u_g$ relating $g(\pi)$ to $\pi$ assemble into a *character* $\lambda:H\to F^*$ of a subgroup $H$; $F$-purity forces $\lambda\equiv 1$, which collapses "$g(\pi)$ is an associate of $\pi$" into "$g(\pi)=\pi$." Building the right $H$ and $\lambda$ is the whole game.
- **(d)–(e)** are then bookkeeping over a UFD: the orbit consists of genuinely distinct primes, so their product is $G$-invariant and, by careful cancellation in a domain, prime in $R^G$.

## The Key Insight

The units of $R=F[x_1,\dots,x_n]$ are exactly the nonzero constants $F^*$. So if $g(\pi)$ is an *associate* of $\pi$, then $g(\pi)=u_g\pi$ with $u_g\in F^*$. The assignment $g\mapsto u_g$, on the subgroup $H$ of all such $g$, is a **homomorphism $H\to F^*$** (because $G$ fixes $F$, so constants pass through). **$F$-purity says this homomorphism is trivial**, i.e. $u_g=1$, i.e. $g(\pi)=\pi$. Therefore the $G$-orbit of $\pi$ has **no associate ambiguity**: any two orbit elements are either *equal* or *non-associate distinct primes*. Consequently the orbit-product
$$
G(\pi)=\prod_{\delta\in G\cdot\pi}\delta
$$
is a well-defined $G$-invariant "norm" of $\pi$, and it is prime in $R^G$ — the mechanism by which prime factorization descends from $R$ to the invariant subring.

## Complete Proof

Write $R=F[x_1,\dots,x_n]$, a UFD whose units are $R^\times=F^*$ (nonzero constants). Recall $G$ $F$-pure means: for every subgroup $H\le G$ and every homomorphism $\lambda:H\to F^*$, $\lambda\equiv 1$.

### Part (a): $|G|$ odd $\Rightarrow$ $G$ is $\mathbb{Q}$-pure

Let $H\le G$ and $\lambda:H\to\mathbb{Q}^*$ a homomorphism. For $h\in H$, its order $k$ divides $|H|$, which divides the odd number $|G|$, so $k$ is odd. Then $\lambda(h)^k=\lambda(h^k)=\lambda(1)=1$, so $\lambda(h)$ is a $k$-th root of unity in $\mathbb{Q}^*$. But the only roots of unity in $\mathbb{Q}$ are $\pm 1$, and $(-1)^k=-1\ne 1$ for odd $k$; hence $\lambda(h)=1$. As $h$ was arbitrary, $\lambda\equiv 1$, so $G$ is $\mathbb{Q}$-pure. $\qquad\checkmark$

*(The point: the torsion subgroup of $\mathbb{Q}^*$ is $\{\pm 1\}\cong\mathbb{Z}/2$, which an odd-order group cannot hit nontrivially.)*

### Part (b): $g(\alpha)$ is prime $\iff$ $\alpha$ is prime

Each $g\in G$ is a ring automorphism of $R$, hence carries the ring structure isomorphically. In particular $g(\alpha)=0\iff\alpha=0$ and $g(\alpha)\in R^\times\iff\alpha\in R^\times$ (automorphisms preserve units). For primality, $g$ maps the principal ideal $(\alpha)$ to $(g(\alpha))$ and induces a ring isomorphism $R/(\alpha)\cong R/(g(\alpha))$; one quotient is an integral domain iff the other is. Since "$\alpha$ prime" $\iff$ "$(\alpha)$ is a nonzero prime ideal" $\iff$ "$R/(\alpha)$ is a nonzero domain," we conclude $g(\alpha)$ is prime iff $\alpha$ is. $\qquad\checkmark$

### Part (c): for prime $\pi$, either $g(\pi)=\pi$ or $g(\pi),\pi$ are distinct primes

Let $H=\{g\in G:\ g(\pi)\ \text{is an associate of}\ \pi\}=\{g\in G:\ g(\pi)\in F^*\pi\}$. For $g\in H$ write $g(\pi)=u_g\pi$ with $u_g\in F^*$; this $u_g$ is unique since $R$ is a domain and $\pi\ne 0$.

**$H$ is a subgroup and $\lambda(g):=u_g$ is a homomorphism $H\to F^*$.** For $g,g'\in H$, using that $g$ fixes the constant $u_{g'}\in F\subseteq R$,
$$
(gg')(\pi)=g(u_{g'}\pi)=u_{g'}\,g(\pi)=u_{g'}u_g\,\pi,
$$
so $gg'\in H$ with $u_{gg'}=u_g u_{g'}$; the identity has $u_1=1$; and from $g(\pi)=u_g\pi$ we get $g^{-1}(\pi)=u_g^{-1}\pi$, so $g^{-1}\in H$. Thus $H\le G$ and $\lambda:H\to F^*$, $\lambda(g)=u_g$, is a homomorphism.

By **$F$-purity**, $\lambda\equiv 1$: for every $g\in H$, $u_g=1$, i.e. $g(\pi)=\pi$. Therefore, for any $g\in G$: if $g\in H$ then $g(\pi)=\pi$; if $g\notin H$ then $g(\pi)$ is not an associate of $\pi$, so $g(\pi)$ and $\pi$ are distinct primes (both prime by (b)). $\qquad\checkmark$

### Part (d): $G(\pi)$ is $G$-invariant, and divides every $G$-fixed multiple of $\pi$

Let $O=\{g(\pi):g\in G\}$ be the orbit. By part (c) (applied to $g^{-1}g'$, whose action on $\pi$ is an associate of $\pi$ iff $g(\pi),g'(\pi)$ are associates), **distinct elements of $O$ are non-associate primes**; so the "distinct primes of the form $g(\pi)$" are exactly the distinct *elements* $\delta_1,\dots,\delta_r$ of $O$, and $G(\pi)=\delta_1\cdots\delta_r$.

**$G(\pi)$ is fixed by $G$.** Any $h\in G$ permutes $O$ as a set: $h(\delta_i)=h(g_i(\pi))=(hg_i)(\pi)\in O$, and $h$ is injective, so $\delta_i\mapsto h(\delta_i)$ is a bijection of $\{\delta_1,\dots,\delta_r\}$. Since $h$ is a ring homomorphism,
$$
h(G(\pi))=\prod_i h(\delta_i)=\prod_i \delta_i=G(\pi).
$$
So $G(\pi)\in R^G$.

**Divisibility.** Suppose $\alpha\in R^G$ and $\pi\mid\alpha$, say $\alpha=\pi\beta$. For each $g\in G$, applying $g$ and using $g(\alpha)=\alpha$ gives $\alpha=g(\pi)\,g(\beta)$, so $g(\pi)\mid\alpha$. Hence every $\delta_i\in O$ divides $\alpha$. The $\delta_i$ are pairwise non-associate primes in the UFD $R$, so in the factorization of $\alpha$ each appears (to distinct prime slots); therefore their product divides $\alpha$:
$$
G(\pi)=\delta_1\cdots\delta_r\ \big|\ \alpha. \qquad\checkmark
$$

### Part (e): $G(\pi)$ is a prime element of the invariant ring $R^G$

By part (d), $G(\pi)\in R^G$. It is nonzero (product of nonzero primes) and not a unit (it is a product of non-constant polynomials, so non-constant, hence $\notin F^*=R^\times\supseteq (R^G)^\times$). It remains to verify the prime divisibility property *inside* $R^G$.

Let $\alpha,\beta\in R^G$ with $G(\pi)\mid\alpha\beta$ in $R^G$ (hence in $R$). Since $\pi$ is one of the factors of $G(\pi)$ (take $g=1$), $\pi\mid\alpha\beta$ in $R$; as $\pi$ is prime in $R$, $\pi\mid\alpha$ or $\pi\mid\beta$. Say $\pi\mid\alpha$. Now $\alpha\in R^G$ is $G$-fixed with $\pi\mid\alpha$, so by part (d), $G(\pi)\mid\alpha$ in $R$: write $\alpha=G(\pi)\gamma$, $\gamma\in R$.

**$\gamma\in R^G$.** For each $g\in G$, applying $g$ to $\alpha=G(\pi)\gamma$ and using that $\alpha,G(\pi)$ are fixed gives $\alpha=G(\pi)\,g(\gamma)$, so $G(\pi)\gamma=G(\pi)\,g(\gamma)$; since $R$ is a domain and $G(\pi)\ne 0$, $\gamma=g(\gamma)$. Thus $\gamma\in R^G$, and $G(\pi)\mid\alpha$ in $R^G$.

Hence $G(\pi)\mid\alpha\beta$ in $R^G$ implies $G(\pi)\mid\alpha$ or $G(\pi)\mid\beta$ in $R^G$. Together with $G(\pi)\ne 0$ non-unit, $G(\pi)$ is a **prime element of $R^G$**. $\qquad\blacksquare$

### Remark — orbit-products as norms, and where purity is essential

The construction $\pi\mapsto G(\pi)=\prod_{g}g(\pi)$ is a *relative norm* down to the invariant ring, and parts (d)–(e) show it sends primes of $R$ to primes of $R^G$ — the algebraic skeleton of how prime factorization behaves under a finite group action (the affine analogue of how primes split/ramify in rings of invariants and in extensions of Dedekind domains). The hypothesis of **$F$-purity is exactly what removes the unit ambiguity**: without it, $g(\pi)$ could be a *nontrivial* associate $u_g\pi$, the "distinct primes in the orbit" would be ill-defined (or the product would pick up a nontrivial unit character and fail to be invariant), and the descent would break. Part (a) supplies a clean sufficient condition for purity — odd order over $\mathbb{Q}$ — because the only obstruction is torsion in $F^*$, which for $\mathbb{Q}$ is just $\{\pm 1\}$. The same character-triviality idea is the engine behind Kummer/Hilbert-90-type arguments (cf. b95J04): a map into $F^*$ built from a group action is forced to be trivial by an arithmetic constraint on roots of unity.

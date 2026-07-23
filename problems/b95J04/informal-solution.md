<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b95J04: Kummer theory — cyclic degree-p extensions are exactly the radical ones

## Why It's Hard

This is a complete, seven-part development of **Kummer theory** for $\mathbb{Z}/p$-extensions, and the difficulty is that the parts are a single chain: a slip in the early setup (that $z$ is a *primitive* $p$-th root of unity and $x^p-1$ splits with distinct roots) collapses everything later. The two halves go in opposite directions and require different machinery:

- **(a)–(e): radical $\Rightarrow$ cyclic.** Given $\alpha$ with $\alpha^p=\omega\in F$, show $F(\alpha)/F$ is Galois with group $\mathbb{Z}/p$. The work is recognizing $F(\alpha)$ as a *splitting field of a separable polynomial* (the roots are $z^i\alpha$), and that the Galois action $\sigma(\alpha)=z^{i(\sigma)}\alpha$ encodes an embedding $G\hookrightarrow\mathbb{Z}/p$.
- **(f)–(g): cyclic $\Rightarrow$ radical.** This is the hard converse: out of an abstract cyclic extension, *manufacture* a radical generator $\alpha$ with $\sigma(\alpha)=z\alpha$. The tool is the **Lagrange resolvent** $\sum_j z^{-j}\sigma^j(\beta)$, and proving it is nonzero for some $\beta$ requires **Dedekind's linear independence of characters** — this is essentially Hilbert's Theorem 90. Spotting the resolvent and knowing why it cannot vanish identically is the crux.

The constant trap is characteristic $p$: there $x^p-1=(x-1)^p$ has no root $\ne 1$, so the hypothesis silently forces $\operatorname{char}F\ne p$ (part a).

## The Key Insight

A primitive $p$-th root of unity $z\in F$ is the **bridge between radicals and the Galois action**: multiplication by powers of $z$ is exactly how $\sigma$ moves a radical around.

- Forward: if $\alpha^p\in F$ then every $\sigma\in G$ sends $\alpha$ to another $p$-th root of $\omega$, i.e. $\sigma(\alpha)=z^{i(\sigma)}\alpha$; the map $\sigma\mapsto i(\sigma)\bmod p$ is an injective homomorphism into $\mathbb{Z}/p$, an isomorphism by primality.
- Backward: given a generator $\sigma$ of a cyclic order-$p$ group, the **Lagrange resolvent**
$$
\alpha=\sum_{j=0}^{p-1}z^{-j}\sigma^j(\beta)\quad\text{satisfies}\quad \sigma(\alpha)=z\alpha
$$
(a cyclic reindexing), is nonzero for some $\beta$ (independence of characters), and has $\sigma(\alpha^p)=z^p\alpha^p=\alpha^p$, so $\alpha^p\in E^G=F$ — a radical generator.

The eigenvalue $z$ of the operator $\sigma$ on $E$ is the single object linking "$\alpha^p\in F$" and "$\operatorname{Gal}\cong\mathbb{Z}/p$."

## Complete Proof

Let $p$ be prime and $F$ a field in which $x^p-1$ has a root $z\ne 1$.

### Part (a): $\operatorname{char}F\ne p$

If $\operatorname{char}F=p$, then in $F[x]$, by the Frobenius/freshman's dream, $x^p-1=x^p-1^p=(x-1)^p$, whose only root is $x=1$. This contradicts the existence of a root $z\ne 1$. Hence $\operatorname{char}F\ne p$. $\qquad\checkmark$

### Part (b): $x^p-1=\prod_{i=1}^{p}(x-z^i)$

Since $z^p=1$, the order of $z$ in $F^\times$ divides $p$; as $p$ is prime and $z\ne 1$, the order is exactly $p$. Thus $z,z^2,\dots,z^p=1$ are $p$ **distinct** elements, each a root of $x^p-1$ (as $(z^i)^p=(z^p)^i=1$). A degree-$p$ polynomial over a field has at most $p$ roots, so these are all of them, and being monic,
$$
x^p-1=\prod_{i=1}^{p}(x-z^i). \qquad\checkmark
$$
In particular $x^p-1$ is separable (distinct roots), and $z$ is a primitive $p$-th root of unity.

### Part (c): with $\alpha\notin F$, $\alpha^p=\omega\in F$, the extension $F(\alpha)/F$ is Galois

Note $\alpha\ne 0$ (else $\alpha=0\in F$). The element $\alpha$ is a root of $x^p-\omega\in F[x]$, and for each $i$, $(z^i\alpha)^p=z^{ip}\omega=\omega$, so $z^i\alpha$ ($i=1,\dots,p$) are roots too. They are distinct (the $z^i$ are distinct by (b) and $\alpha\ne 0$), so
$$
x^p-\omega=\prod_{i=1}^{p}(x-z^i\alpha),
$$
$p$ distinct roots, all lying in $F(\alpha)$ (since $z\in F$). Hence $F(\alpha)$ is the **splitting field** of $x^p-\omega$ over $F$ — a normal extension — and $x^p-\omega$ is **separable** (distinct roots), so $F(\alpha)/F$ is separable. Normal $+$ separable $=$ **Galois**. $\qquad\checkmark$

### Part (d): each $\sigma\in G$ satisfies $\sigma(\alpha)=z^{i(\sigma)}\alpha$ for a unique $i(\sigma)\in[1,p]$

Let $G=\operatorname{Gal}(F(\alpha)/F)$ and $\sigma\in G$. Since $\sigma$ fixes $F$,
$$
\sigma(\alpha)^p=\sigma(\alpha^p)=\sigma(\omega)=\omega,
$$
so $\sigma(\alpha)$ is a root of $x^p-\omega$, hence $\sigma(\alpha)=z^{i}\alpha$ for some $i\in\{1,\dots,p\}$ by part (c). Uniqueness: if $z^j\alpha=z^k\alpha$ with $j,k\in[1,p]$, then $z^{j-k}=1$ (as $\alpha\ne 0$), so $p\mid j-k$ (order of $z$ is $p$), forcing $j=k$ in $[1,p]$. So $i(\sigma)$ is well-defined and unique. $\qquad\checkmark$

### Part (e): $\sigma\mapsto i(\sigma)\bmod p$ is an isomorphism $G\xrightarrow{\sim}\mathbb{Z}/p$

**Homomorphism.** For $\sigma,\tau\in G$, using that $\sigma$ fixes $z\in F$,
$$
\sigma\tau(\alpha)=\sigma(z^{i(\tau)}\alpha)=z^{i(\tau)}\sigma(\alpha)=z^{i(\tau)}z^{i(\sigma)}\alpha=z^{\,i(\sigma)+i(\tau)}\alpha,
$$
so $i(\sigma\tau)\equiv i(\sigma)+i(\tau)\pmod p$. Thus $\sigma\mapsto i(\sigma)\bmod p$ is a homomorphism $G\to\mathbb{Z}/p$.

**Injective.** If $i(\sigma)\equiv 0$, then $\sigma(\alpha)=z^{p}\alpha=\alpha$; since $\sigma$ also fixes $F$, it fixes $F(\alpha)$, so $\sigma=\mathrm{id}$. The kernel is trivial.

**Onto.** Since $\alpha\notin F$, $F(\alpha)\supsetneq F$, so $|G|=[F(\alpha):F]>1$. An injective homomorphism from a nontrivial group into $\mathbb{Z}/p$ (with $p$ prime) has image a nontrivial subgroup of $\mathbb{Z}/p$, which must be all of $\mathbb{Z}/p$. Hence the map is an isomorphism $G\cong\mathbb{Z}/p$. $\qquad\checkmark$

*(In particular $[F(\alpha):F]=p$, so $x^p-\omega$ is irreducible over $F$.)*

### Part (f): in a cyclic order-$p$ extension $E/F$, some $\alpha\ne 0$ has $\sigma(\alpha)=z\alpha$

Let $G=\operatorname{Gal}(E/F)=\langle\sigma\rangle$, $|G|=p$, $\sigma\ne 1$. Define the **Lagrange resolvent** of $\beta\in E$:
$$
\alpha(\beta)=\sum_{j=0}^{p-1} z^{-j}\,\sigma^j(\beta).
$$
Applying $\sigma$ and reindexing $k=j+1$ (with $\sigma^p=\mathrm{id}$, $z^{-p}=1$, so the $k=p$ term equals the $k=0$ term):
$$
\sigma(\alpha(\beta))=\sum_{j=0}^{p-1}z^{-j}\sigma^{j+1}(\beta)=z\sum_{k=1}^{p}z^{-k}\sigma^{k}(\beta)=z\sum_{k=0}^{p-1}z^{-k}\sigma^{k}(\beta)=z\,\alpha(\beta).
$$
So $\sigma(\alpha(\beta))=z\,\alpha(\beta)$ for **every** $\beta$. It remains to find $\beta$ with $\alpha(\beta)\ne 0$. The distinct automorphisms $1,\sigma,\dots,\sigma^{p-1}$ (distinct since $\sigma$ has order $p$) are **linearly independent over $E$** by **Dedekind's theorem on independence of characters**. Hence the operator $\sum_{j=0}^{p-1}z^{-j}\sigma^j$, having nonzero coefficients $z^{-j}$, is not the zero map; so there exists $\beta\in E$ with $\alpha:=\alpha(\beta)\ne 0$. This $\alpha$ satisfies $\sigma(\alpha)=z\alpha$. $\qquad\checkmark$

### Part (g): $\alpha\notin F$, $\alpha^p\in F$, and $E=F(\alpha)$

Take $\alpha\ne 0$ from part (f) with $\sigma(\alpha)=z\alpha$.

**$\alpha^p\in F$.** Since $z^p=1$,
$$
\sigma(\alpha^p)=\sigma(\alpha)^p=(z\alpha)^p=z^p\alpha^p=\alpha^p,
$$
so $\alpha^p$ is fixed by $\sigma$, hence by all of $G=\langle\sigma\rangle$. As $E/F$ is Galois, the fixed field is $E^G=F$, so $\alpha^p\in F$.

**$\alpha\notin F$.** If $\alpha\in F$, then $\sigma(\alpha)=\alpha$ (σ fixes $F$); but $\sigma(\alpha)=z\alpha$, so $(z-1)\alpha=0$, and $\alpha\ne 0$ gives $z=1$ — contradicting $z\ne 1$. So $\alpha\notin F$.

**$E=F(\alpha)$.** Then $F\subsetneq F(\alpha)\subseteq E$ and $[E:F]=|G|=p$ is prime, so $[F(\alpha):F]\in\{1,p\}$ divides $p$ and exceeds $1$, forcing $[F(\alpha):F]=p=[E:F]$. Hence $F(\alpha)=E$. $\qquad\blacksquare$

### Remark — the Kummer correspondence

Together the parts prove the **Kummer theorem** for exponent $p$: when $F$ contains a primitive $p$-th root of unity (forcing $\operatorname{char}F\ne p$), the degree-$p$ **cyclic** extensions of $F$ are *exactly* the **radical** extensions $F(\alpha)$ with $\alpha^p\in F$, and $\operatorname{Gal}\cong\mathbb{Z}/p$. Parts (a)–(e) are "radical $\Rightarrow$ cyclic"; (f)–(g) are the converse "cyclic $\Rightarrow$ radical," whose engine is **Hilbert's Theorem 90**: the element of norm... more precisely, $\sigma(\alpha)/\alpha=z$ has norm $\prod_{j}\sigma^j(z)=z^p=1$, and Theorem 90 (here in its additive-resolvent guise via Dedekind independence) produces the eigenvector $\alpha$. The presence of $\mu_p\subseteq F$ is essential throughout — it is what makes $x^p-1$ split (b) so that $\sigma$ is diagonalizable with the $z^i$ as available eigenvalues, and it is exactly the hypothesis that fails in the inseparable Artin–Schreier theory of degree-$p$ extensions in characteristic $p$.

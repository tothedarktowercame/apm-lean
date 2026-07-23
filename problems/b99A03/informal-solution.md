<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b99A03: The minimal polynomial of α as the product over the conjugates σᵢ(α)

## Why It's Hard

The goal is to *construct* the minimal polynomial of $\alpha$ over $F$ purely
group-theoretically, as $g(x)=\prod_i(x-\sigma_i(\alpha))$ over coset representatives of
$H=\operatorname{Gal}(E/F(\alpha))$ in $G=\operatorname{Gal}(E/F)$. The crux is realizing
that $H$ is exactly the **stabilizer of $\alpha$**, so cosets of $H$ correspond
bijectively to the *distinct conjugates* $\sigma_i(\alpha)$ (part a); the rest is showing
the coefficients are $G$-invariant (hence in $F$) by checking that any $\tau\in G$ merely
permutes the roots — which is where (a) and (b) are spent — and then a degree count pins
$g$ as *the* minimal polynomial.

## The Key Insight

$H=\operatorname{Gal}(E/F(\alpha))=\{\,h\in G: h(\alpha)=\alpha\,\}$ is the stabilizer of
$\alpha$. Hence:
- **(a)** $\sigma H=\tau H\iff\tau^{-1}\sigma\in H\iff\tau^{-1}\sigma(\alpha)=\alpha\iff
  \sigma(\alpha)=\tau(\alpha)$ — cosets $\leftrightarrow$ conjugate-values.
- **(b)** $gH\mapsto \tau gH$ is a bijection of $G/H$, so $\{\tau\sigma_i\}$ is again a
  full set of reps.
- **(c)** Any $\tau\in G$ sends the root list $(\sigma_i(\alpha))$ to $(\tau\sigma_i
  (\alpha))$, a permutation of the same list (by a,b), so it fixes every coefficient of
  $g$; thus $g\in (E^G)[x]=F[x]$.
- **(d)** $g$ is monic in $F[x]$, vanishes at $\alpha$, and $\deg g=[G:H]=[F(\alpha):F]=
  \deg(\text{min poly})$, so $g$ is the minimal polynomial.

## Complete Proof

$E/F$ is finite Galois, $G=\operatorname{Gal}(E/F)$, $H=\operatorname{Gal}(E/F(\alpha))$,
and $\sigma_1,\dots,\sigma_n$ are left coset representatives of $H$ in $G$, so $n=[G:H]$.

First note $H$ is the stabilizer of $\alpha$: an element $h\in G$ fixes $F(\alpha)=F[\alpha]$
pointwise iff it fixes $\alpha$ (it already fixes $F$), so
$$
H=\{h\in G: h(\alpha)=\alpha\}.
$$

### (a) $\sigma H=\tau H\iff\sigma(\alpha)=\tau(\alpha)$

$$
\sigma H=\tau H\iff \tau^{-1}\sigma\in H\iff (\tau^{-1}\sigma)(\alpha)=\alpha\iff
\sigma(\alpha)=\tau(\alpha),
$$
the last step applying the automorphism $\tau$ to both sides (and its inverse for the
converse). $\quad\checkmark$

### (b) $\tau\sigma_1,\dots,\tau\sigma_n$ is also a complete set of representatives

Left multiplication by $\tau$ on the coset space, $gH\mapsto \tau gH$, is a bijection of
$G/H$ to itself (with inverse $gH\mapsto\tau^{-1}gH$). Applying it to the complete,
irredundant list of cosets $\sigma_1H,\dots,\sigma_nH$ yields $\tau\sigma_1H,\dots,
\tau\sigma_nH$, which is therefore again a list of all $n$ cosets, each exactly once.
Hence $\tau\sigma_1,\dots,\tau\sigma_n$ is a complete set of left coset representatives.
$\quad\checkmark$

### (c) $g(x)=\prod_{i=1}^n(x-\sigma_i(\alpha))\in F[x]$

By (a), the values $\sigma_1(\alpha),\dots,\sigma_n(\alpha)$ are **distinct** (equal
values would mean equal cosets, i.e. equal indices). Let $\tau\in G$ act on $g$ by acting
on its coefficients; since $g=\prod_i(x-\sigma_i(\alpha))$, this gives
$$
\tau(g)(x)=\prod_{i=1}^n\big(x-\tau(\sigma_i(\alpha))\big)=\prod_{i=1}^n\big(x-(\tau\sigma_i)(\alpha)\big).
$$
By (b), $\{\tau\sigma_i\}$ is a complete set of coset representatives, so each
$\tau\sigma_i$ lies in the same coset as exactly one $\sigma_{\pi(i)}$ (for a permutation
$\pi$ of $\{1,\dots,n\}$); by (a), $(\tau\sigma_i)(\alpha)=\sigma_{\pi(i)}(\alpha)$.
Therefore
$$
\tau(g)(x)=\prod_{i=1}^n\big(x-\sigma_{\pi(i)}(\alpha)\big)=\prod_{j=1}^n\big(x-\sigma_j(\alpha)\big)=g(x):
$$
$\tau$ merely permutes the roots, leaving $g$ unchanged. Hence every coefficient of $g$ is
fixed by every $\tau\in G$, so the coefficients lie in $E^G$. As $E/F$ is Galois, $E^G=F$,
so $g(x)\in F[x]$. $\quad\checkmark$

### (d) $g(x)$ is the minimal polynomial of $\alpha$ over $F$

Let $m(x)\in F[x]$ be the minimal polynomial of $\alpha$ over $F$.

- $g$ **vanishes at $\alpha$:** the coset $H$ is represented by some $\sigma_i\in H$, and
  $\sigma_i(\alpha)=\alpha$ (as $H$ is the stabilizer), so $(x-\alpha)$ is one of the
  factors and $g(\alpha)=0$.
- $g$ is **monic** of degree $n$ and lies in $F[x]$ (part c).
- Since $g(\alpha)=0$ and $g\in F[x]$, the minimal polynomial divides $g$: $m\mid g$.
- Degrees: $\deg g=n=[G:H]$. By the Galois correspondence $[G:H]=[F(\alpha):F]$, and
  $[F(\alpha):F]=\deg m$. Hence $\deg g=\deg m$.

From $m\mid g$, $\deg m=\deg g$, and both monic, we get $g=m$. Therefore $g(x)$ is the
minimal polynomial of $\alpha$ over $F$. $\quad\blacksquare$

### Remark

The content is the orbit–stabilizer principle in Galois dress: the conjugates of $\alpha$
are the $G$-orbit $\{\sigma(\alpha)\}$, whose size is the index $[G:\operatorname{Stab}
(\alpha)]=[G:H]=[F(\alpha):F]$, and these are exactly the (distinct) roots of the minimal
polynomial. Part (c) is the statement that a polynomial whose root-multiset is
$G$-stable has $F$-rational coefficients — the "averaging over the orbit" that produces
$F$-rationality. This simultaneously reproves that $[F(\alpha):F]$ equals the number of
distinct conjugates of $\alpha$ and that $m(x)=\prod_{\beta\,\text{conj. of }\alpha}
(x-\beta)$ splits completely in $E$ with simple roots (separability of $E/F$).

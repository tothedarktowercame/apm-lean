<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b94J01: Finite abelian groups, when Z/m ⊕ Z/n is cyclic, and why finite subgroups of a field are cyclic

## Why It's Hard

Parts (a)–(b) are bookkeeping with the structure theorem and the lcm of orders. The
substance is (c): the statement "a finite subgroup of $K^\times$ is cyclic" (the source
of primitive roots mod $p$) is *false* for general abelian groups of the same order, so
the proof must use the **field** hypothesis in an essential way. It enters through one
sharp fact — a degree-$d$ polynomial has at most $d$ roots in a field — which fails in a
ring like $\mathbb{Z}/8$, where $x^2-1$ has four roots and indeed $(\mathbb{Z}/8)^\times$
is not cyclic. The other half is the purely group-theoretic lemma that a finite abelian
group *attains* its exponent (some element has order equal to the lcm of all orders).

## The Key Insight

- **(b)** $\mathbb{Z}/m\oplus\mathbb{Z}/n$ has order $mn$ and maximal element order
  $\operatorname{lcm}(m,n)$; it is cyclic iff these agree, i.e.
  $\operatorname{lcm}(m,n)=mn\iff\gcd(m,n)=1$.
- **(c)** Let $d$ be the exponent of $G$ (lcm of all element orders). A finite abelian
  group has an element of order $d$, so $|G|\ge d$. But every $g\in G$ satisfies $g^d=1$,
  so all $|G|$ elements are roots of $x^d-1$ in $K$; a field forces $|G|\le d$. Hence
  $|G|=d$ and that element generates $G$.

## Complete Proof

### (a) The Fundamental Theorem of Finite Abelian Groups

Every finite abelian group $G$ is isomorphic to a direct sum of cyclic groups, in two
standard (equivalent) normal forms, each unique:

- **Invariant-factor form.** There are unique integers $d_1\mid d_2\mid\cdots\mid d_k$
  (each $d_i\ge 2$) with
  $$
  G\cong \mathbb{Z}/d_1\mathbb{Z}\ \oplus\ \mathbb{Z}/d_2\mathbb{Z}\ \oplus\cdots\oplus\ \mathbb{Z}/d_k\mathbb{Z}.
  $$
- **Elementary-divisor (primary) form.** There are prime powers
  $p_1^{a_1},\dots,p_r^{a_r}$ (the primes need not be distinct), unique up to ordering,
  with
  $$
  G\cong \bigoplus_{j=1}^{r}\mathbb{Z}/p_j^{\,a_j}\mathbb{Z}.
  $$

The two are related by the Chinese Remainder Theorem; in particular $|G|=\prod d_i=\prod
p_j^{a_j}$, and the largest invariant factor $d_k$ is the **exponent** of $G$.

### (b) When is $\mathbb{Z}/m\mathbb{Z}\oplus\mathbb{Z}/n\mathbb{Z}$ cyclic?

**Claim.** $\mathbb{Z}/m\oplus\mathbb{Z}/n$ is cyclic $\iff \gcd(m,n)=1$.

The group has order $mn$, so it is cyclic iff it has an element of order $mn$. The order
of an element $(a,b)$ is $\operatorname{lcm}(\operatorname{ord}(a),\operatorname{ord}(b))$,
which divides $\operatorname{lcm}(m,n)$; and the value $\operatorname{lcm}(m,n)$ is
attained by $(1,1)$ (orders $m$ and $n$). So the maximal element order is exactly
$\operatorname{lcm}(m,n)$. Therefore
$$
\text{cyclic}\iff \operatorname{lcm}(m,n)=mn .
$$
Since $\operatorname{lcm}(m,n)\cdot\gcd(m,n)=mn$, this holds iff $\gcd(m,n)=1$.

($\Rightarrow$ direction restated: if cyclic then the max order $mn=\operatorname{lcm}(m,n)$,
forcing $\gcd=1$. $\Leftarrow$: if $\gcd(m,n)=1$ then $(1,1)$ has order $mn$ — this is
exactly the CRT isomorphism $\mathbb{Z}/mn\cong\mathbb{Z}/m\oplus\mathbb{Z}/n$.)
$\quad\checkmark$

### (c) A finite subgroup $G\subseteq K^\times$ is cyclic

$G$ is a finite abelian group (a subgroup of the abelian group $K^\times$). Let
$$
d=\exp(G)=\operatorname{lcm}\{\operatorname{ord}(g): g\in G\}
$$
be its exponent.

**Lemma (the exponent is attained).** In a finite abelian group there is an element of
order $d$. *Proof.* It suffices to show: if $a$ has order $r$ and $b$ has order $s$, some
element has order $\operatorname{lcm}(r,s)$; then iterating over all elements produces
one of order equal to the lcm of all orders, namely $d$. For the two-element claim,
factor $\operatorname{lcm}(r,s)=\prod_p p^{e_p}$; for each prime $p$, one of $r,s$
contributes the full $p^{e_p}$, and an appropriate power of $a$ or $b$ has order exactly
$p^{e_p}$. In an abelian group, a product of elements of pairwise coprime orders
$p^{e_p}$ has order $\prod_p p^{e_p}=\operatorname{lcm}(r,s)$. $\square$

By the lemma, there is $g_0\in G$ with $\operatorname{ord}(g_0)=d$, so the cyclic
subgroup $\langle g_0\rangle$ has $d$ elements and
$$
|G|\ \ge\ d. \tag{1}
$$
On the other hand, $d$ is the exponent, so $g^d=1$ for **every** $g\in G$. Thus every
element of $G$ is a root in $K$ of the polynomial
$$
x^d-1\in K[x].
$$
Over a field, a nonzero polynomial of degree $d$ has at most $d$ roots, so $G$ — all of
whose elements are roots — has at most $d$ elements:
$$
|G|\ \le\ d. \tag{2}
$$
Combining (1) and (2), $|G|=d=\operatorname{ord}(g_0)$, so $\langle g_0\rangle=G$ and
$G$ is cyclic. $\quad\blacksquare$

### Remark

The field hypothesis is used exactly once — the bound "$x^d-1$ has at most $d$ roots" —
and it is indispensable. In a general ring the bound fails: in $(\mathbb{Z}/8)^\times=
\{1,3,5,7\}$ every element squares to $1$, so the exponent is $2$ while the order is $4$;
$x^2-1$ has four roots mod $8$, and the group is the non-cyclic Klein four-group. The
classic consequence of (c) is that $\mathbb{F}_q^\times$ is cyclic for every finite
field $\mathbb{F}_q$ — i.e. primitive roots exist — and more generally any finite
multiplicative group of any field (including subgroups of $\mathbb{C}^\times$, which are
the groups of roots of unity $\mu_n$).

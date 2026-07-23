<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b98J02: The Galois group acts transitively on the primes lying over a fixed prime

## Why It's Hard

This is the cornerstone splitting theorem of algebraic number theory — $\operatorname{Gal}
(M/L)$ permutes the primes of $B$ over a fixed prime $q$ of $A$ *transitively* — and its
proof braids three different tools that look unrelated: **prime avoidance** (an ideal
inside a finite union of primes lies in one of them), a **norm** $\prod_{g}g(x)$ (which
must be shown to land in $A$, using Galois invariance plus integral-closedness), and the
**incomparability** of primes over the same base prime in an integral extension. The
clever step is the contrapositive: if $P'$ is *not* in the orbit of $P$, the norm forces
$P'$ inside the union of the orbit, and prime avoidance then traps it inside a single
conjugate — a contradiction with not being in the orbit.

## The Key Insight

- **(a)** If $I\subseteq P_1\cup\cdots\cup P_n$ (primes), pick $x_i\in I$ with $x_i\in
  P_i$ but $x_i\notin P_j\ (j\neq i)$; then $y=x_1+x_2x_3\cdots x_n\in I$ avoids every
  $P_i$ — contradiction unless $I\subseteq$ some $P_i$.
- **(b)** $y=\prod_{g\in G}g(x)$ is $G$-invariant (so in $L=M^G$) and integral over $A$
  (so in $B$), hence in $B\cap L=A$; the factor $g=e$ gives $x\mid y$, so $y\in P$. Thus
  $y\in P\cap A$.
- **(c)** For $P,P'$ over $q$: take $x\in P'$; $\prod_g g(x)\in P'\cap A=q\subseteq P$, so
  some $g(x)\in P$, i.e. $x\in g^{-1}(P)$. Hence $P'\subseteq\bigcup_g g(P)$; by (a)
  $P'\subseteq h(P)$, and incomparability forces $P'=h(P)$.

## Complete Proof

Setup: $A\subseteq B$ domains with fraction fields $L\subseteq M$, $M/L$ finite Galois
with group $G$, $B$ the integral closure of $A$ in $M$, and $A$ integrally closed
($B\cap L=A$). Each $g\in G$ fixes $A$ and maps integral elements to integral elements,
so $g(B)=B$; thus $G$ acts on $B$ by ring automorphisms.

### (a) Prime avoidance

Let $I\subseteq B$ be an ideal with $I\subseteq P_1\cup\cdots\cup P_n$, the $P_i$ prime.
We may assume the cover is **irredundant** (discard any $P_i$ with $I\subseteq\bigcup_{j
\neq i}P_j$ and induct on $n$; the base case $n=1$ is trivial). Suppose, for
contradiction, $I\not\subseteq P_i$ for every $i$.

Irredundancy means $I\not\subseteq\bigcup_{j\neq i}P_j$, so for each $i$ there is
$x_i\in I$ with $x_i\notin P_j$ for all $j\neq i$; since $I\subseteq\bigcup P_k$ forces
$x_i$ into some $P_k$, necessarily $x_i\in P_i$. Form
$$
y=x_1+x_2x_3\cdots x_n\in I .
$$
- Modulo $P_1$: $x_1\in P_1$, while each $x_j\notin P_1$ ($j\ge2$) and $P_1$ is prime, so
  $x_2\cdots x_n\notin P_1$; hence $y\notin P_1$.
- Modulo $P_i$, $i\ge2$: $x_1\notin P_i$, while the product $x_2\cdots x_n$ contains the
  factor $x_i\in P_i$, so $x_2\cdots x_n\in P_i$; hence $y\equiv x_1\not\equiv0\pmod{P_i}$,
  i.e. $y\notin P_i$.

So $y\in I$ but $y\notin P_i$ for all $i$, contradicting $I\subseteq\bigcup P_i$.
Therefore $I\subseteq P_i$ for some $i$. $\quad\checkmark$

### (b) The norm of an element of $P$ lies in $P\cap A$

Let $P$ be prime in $B$ and $x\in P$. Put
$$
y=\prod_{g\in G}g(x).
$$
**$y\in A$.** For any $h\in G$, $h(y)=\prod_g h(g(x))=\prod_{g}(hg)(x)=y$ (the map
$g\mapsto hg$ permutes $G$). So $y$ is fixed by all of $G$, hence $y\in M^G=L$ (as $M/L$
is Galois). Also each $g(x)\in g(B)=B$, and $B$ is a ring, so $y\in B$. Therefore $y\in
B\cap L=A$.
**$y\in P$.** The factor for $g=e$ is $x\in P$, and $y=x\cdot\prod_{g\neq e}g(x)$ with the
remaining product in $B$; since $P$ is an ideal of $B$, $y\in P$.
Hence $y\in P\cap A$. $\quad\checkmark$
(Concretely $y=N_{M/L}(x)$ is the field norm; the point is that it lands in $A$ and in
$P$.)

### (c) $G$ acts transitively on the primes over $q$

Fix a prime $q$ of $A$, and let $P,P'$ be primes of $B$ lying over $q$ (so $P\cap A=
P'\cap A=q$). We must find $g\in G$ with $g(P)=P'$. The orbit $\{g(P):g\in G\}$ is a
finite set of primes (given that $G$ permutes the primes over $q$; note each $g(P)$ also
lies over $q$, since $g(P)\cap A=g(P)\cap g(A)=g(P\cap A)=g(q)=q$ as $q\subseteq A$ is
fixed).

Take any $x\in P'$. By (b) applied to $P'$,
$$
\prod_{g\in G}g(x)\in P'\cap A=q=P\cap A\subseteq P .
$$
Since $P$ is prime and the product lies in $P$, some factor $g(x)\in P$, i.e. $x\in
g^{-1}(P)$. As $x\in P'$ was arbitrary,
$$
P'\subseteq\bigcup_{g\in G}g^{-1}(P)=\bigcup_{h\in G}h(P),
$$
a finite union of primes. By prime avoidance (a), $P'\subseteq h(P)$ for some $h\in G$.

Now $P'$ and $h(P)$ are **both primes of $B$ lying over $q$**. In an integral extension,
two primes lying over the same prime of the base satisfy incomparability: if one is
contained in the other, they are equal. (This is the standard INC property of $B/A$
integral; equivalently, $B/h(P)$ is integral over the field $A/q$, hence a field, so
$h(P)$ is maximal among primes over $q$, forcing $P'=h(P)$.) Therefore
$$
P'=h(P),
$$
so $P'$ lies in the orbit of $P$. Since $P,P'$ were arbitrary primes over $q$, $G$ acts
transitively on the set of primes of $B$ lying over $q$. $\quad\blacksquare$

### Remark

This is the theorem behind decomposition groups and the splitting of primes in Galois
extensions of number fields/Dedekind domains: the residue degree $f$, ramification index
$e$, and the number $g$ of primes over $q$ satisfy $efg=[M:L]$ precisely because $G$
permutes the $g$ primes transitively with stabilizer the decomposition group (of order
$ef$). The proof is a model of how three "soft" commutative-algebra facts combine: prime
avoidance (a) is the combinatorial glue, the norm (b) is the bridge from $B$ down to $A$
made possible by integral-closedness, and incomparability supplies the final rigidity.
Galois-ness enters in exactly one spot — $M^G=L$ in (b) — which is why the conclusion can
fail for non-normal extensions.

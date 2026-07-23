<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b97J02: Zero-dimensional reduced rings embed in (and finitely, equal) products of fields

## Why It's Hard

The five parts assemble the commutative analogue of "semisimple": a $0$-dimensional
reduced ring is a subring of a product of fields, and a finite spectrum makes it the full
product. Each step uses a different tool — $0$-dimensional $\Rightarrow$ primes maximal
(a); the idempotent/von-Neumann-regular hypothesis $\Rightarrow$ no nilpotents and no
prime chains (b); reduced $=$ the embedding is injective (d); CRT closes the gap (e). The
subtle engine is **idempotents**: $e^2=e$ gives $e(1-e)=0$, which both kills nilpotents
and forces a prime to swallow one of $e,1-e$ — collapsing prime chains.

## The Key Insight

- **(a)** $0$-dim makes every prime maximal (a prime sits in a maximal one, and the
  inclusion is forced to be equality), so $R/P$ is a field.
- **(b)** Write $aR=eR$, $e^2=e$: if $a$ is nilpotent then $e=(ab)^n=0$ so $a=ea=0$
  (reduced); and for $P\subseteq Q$, $e(1-e)=0\in P$ forces $a\in P$, so $Q\subseteq P$
  ($0$-dim).
- **(c)** In $\prod F_i$, the "support indicator" $e_i=\mathbf 1[a_i\neq0]$ is an
  idempotent with $aR=eR$, so (b) applies.
- **(d)** $\varphi(a)=(a+P)_P$ has kernel $\bigcap_P P=\{0\}$ (reduced) — injective.
- **(e)** Finitely many primes are pairwise comaximal maximals with intersection $0$, so
  CRT gives $R\cong\prod_P R/P$.

## Complete Proof

$R$ is commutative with $1$.

### (a) $0$-dimensional $\Rightarrow$ $R/P$ is a field for every prime $P$

Let $P$ be prime. Choose a maximal ideal $M\supseteq P$ (possible since $P$ is proper).
$M$ is prime, and $P\subseteq M$, so $0$-dimensionality forces $P=M$. Hence $P$ is
maximal, and $R/P$ is a field. $\quad\checkmark$

### (b) The idempotent hypothesis $\Rightarrow$ $R$ is $0$-dimensional and reduced

Assume: for every $a\in R$ there is an idempotent $e$ (so $e^2=e$) with $aR=eR$. Two
facts we use repeatedly: from $a\in eR$, $a=ea$ (every $x\in eR$ satisfies $ex=x$), and
from $e\in aR$, $e=ab$ for some $b\in R$.

**Reduced.** Suppose $a^n=0$. Take $e$ idempotent with $aR=eR$, and write $e=ab$. Then,
using commutativity and $e=e^n$,
$$
e=e^n=(ab)^n=a^n b^n=0 .
$$
Hence $a=ea=0$. So $R$ has no nonzero nilpotents; equivalently the nilradical
$\bigcap_P P$ is $\{0\}$, i.e. $R$ is reduced.

**$0$-dimensional.** Let $P\subseteq Q$ be primes; we show $Q\subseteq P$. Take any
$a\in Q$ and an idempotent $e$ with $aR=eR$. Then $e(1-e)=e-e^2=0\in P$, and $P$ prime
forces $e\in P$ or $1-e\in P$. Now $e\in aR\subseteq Q$ (as $a\in Q$). If $1-e\in
P\subseteq Q$, then $1=e+(1-e)\in Q$, contradicting that $Q$ is proper. So $1-e\notin P$,
whence $e\in P$, and therefore $a=ea\in P$. Thus $Q\subseteq P$, so $P=Q$: there are no
strict inclusions among primes. $\quad\checkmark$

### (c) A product of fields $\prod_{i\in I}F_i$ is $0$-dimensional and reduced

Let $R=\prod_i F_i$ and $a=(a_i)_i\in R$. Define $e=(e_i)_i$ and $b=(b_i)_i$ by
$$
e_i=\begin{cases}1,&a_i\neq0\\0,&a_i=0\end{cases},\qquad
b_i=\begin{cases}a_i^{-1},&a_i\neq0\\0,&a_i=0.\end{cases}
$$
Then $e^2=e$ (each $e_i\in\{0,1\}$); $ea=a$ since $e_i a_i=a_i$ in every coordinate, so
$a\in eR$; and $ab=e$ since $a_i b_i=e_i$, so $e\in aR$. Hence $aR=eR$ with $e$
idempotent. As this holds for every $a$, part (b) applies and $\prod_i F_i$ is
$0$-dimensional and reduced. $\quad\checkmark$

### (d) The natural map $\varphi$ and its injectivity

Assume $R$ is $0$-dimensional and reduced, and for $P\in\operatorname{Spec}(R)$ put
$F_P=R/P$ (a field, by (a)). Define
$$
\varphi:R\to\prod_{P\in\operatorname{Spec}(R)}F_P,\qquad \varphi(a)=(a+P)_{P} .
$$
This is a ring homomorphism, being the product of the quotient homomorphisms $R\to R/P$.
Its kernel is
$$
\ker\varphi=\{a: a\in P\ \text{for all primes }P\}=\bigcap_{P\in\operatorname{Spec}(R)}P=\{0\},
$$
the last equality because $R$ is reduced. Hence $\varphi$ is injective. $\quad\checkmark$

### (e) Finite spectrum $\Rightarrow$ $\varphi$ is bijective

Suppose $\operatorname{Spec}(R)=\{P_1,\dots,P_n\}$ is finite. By (a) each $P_i$ is
maximal, and distinct maximal ideals are **comaximal**: for $i\neq j$, $P_i+P_j$ is an
ideal strictly larger than the maximal ideal $P_i$ (it contains $P_j\not\subseteq P_i$),
so $P_i+P_j=R$. By the Chinese Remainder Theorem for pairwise comaximal ideals, the map
$$
R\ \longrightarrow\ \prod_{i=1}^{n}R/P_i,\qquad a\mapsto (a+P_i)_i,
$$
is surjective with kernel $P_1\cap\cdots\cap P_n$. But this intersection over *all* primes
is the nilradical, which is $\{0\}$ since $R$ is reduced; so the kernel is $0$. Hence the
map is bijective. Since $\operatorname{Spec}(R)=\{P_1,\dots,P_n\}$, this map is exactly
$\varphi$, so
$$
\varphi:R\ \xrightarrow{\ \sim\ }\ \prod_{P\in\operatorname{Spec}(R)}R/P
$$
is a ring isomorphism. $\quad\blacksquare$

### Remark

The chain identifies the $0$-dimensional reduced rings as the **subdirect products of
fields**, with the finite-spectrum case being an honest finite product
$R\cong\prod_{i=1}^n R/P_i$ — the commutative shadow of Artin–Wedderburn (fields in place
of matrix algebras, because commutative). The hypothesis in (b) is *von Neumann
regularity* ("every principal ideal is generated by an idempotent"), and (b)+(c) show it
is equivalent to "$0$-dimensional and reduced." Idempotents are the bridge throughout:
they are the indicator functions of the clopen pieces of $\operatorname{Spec}(R)$, and a
finite discrete spectrum is what lets the idempotents split $R$ completely into its field
factors.

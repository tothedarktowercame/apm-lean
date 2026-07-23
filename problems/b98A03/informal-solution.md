<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b98A03: The conductor controls prime splitting — minimal splitting forces P = Q₁∩Q₂ = I

## Why It's Hard

This is a five-part development of conductor theory whose payoff (e) is sharp and surprising: if two *distinct* primes $Q_1\ne Q_2$ of $T$ lie over the same prime $P$ of $R$ and agree on **no** intermediate ring except $R$ itself, then $P$ is forced to equal both $Q_1\cap Q_2$ and the conductor $I$. The difficulty is that this conclusion is assembled from four lemmas pulling in different directions, and one must see how they interlock.

Two ideas do the heavy lifting and are easy to miss:

1. **A conductor element bridges $T$ back into $R$** (part b): if $x\in I\setminus P$, then $xt\in R$ for all $t\in T$, which is exactly what forces a *unique* prime over $P$ — the contrapositive engine for (e).
2. **A constant-term criterion** (part c): for $u\in Q$, an element $\sum a_iu^i\in R[u]$ lies in $Q$ iff its constant term $a_0\in P$, because $u\in Q$ annihilates every higher term modulo $Q$. The subtlety is that this is well-defined even though $u$ may be algebraic over $R$ (different representations give constant terms that are simultaneously in or out of $P$).

The final assembly (e) is the clever part: every common element $u\in Q_1\cap Q_2$ generates an intermediate ring $R[u]$ on which the two primes agree (by c–d), so the "agree only on $R$" hypothesis forces $u\in R$, i.e. $Q_1\cap Q_2\subseteq R$ — collapsing the intersection onto $P$ and then onto $I$.

## The Key Insight

The conductor $I=\{r\in R:rT\subseteq R\}$ is the **largest ideal of $T$ contained in $R$** (a), and it governs how primes of $R$ lift to $T$:

- **Away from $I$** ($I\not\subseteq P$): a bridge element $x\in I\setminus P$ satisfies $xt\in R$ for all $t$, so $t\in Q_1\Rightarrow xt\in Q_1\cap R=P\subseteq Q_2$, and primality with $x\notin Q_2$ gives $t\in Q_2$ — **unique lift** $Q_1=Q_2$ (b).
- **The trace on $R[u]$** depends only on the constant term mod $P$ (c), so any two primes through a common $u$ agree on $R[u]$ (d).

Hence if $Q_1\ne Q_2$ lie over $P$ and agree on no intermediate ring but $R$, then $Q_1\cap Q_2\subseteq R$ (each common $u$ would otherwise make $R[u]\ne R$ a place of agreement), forcing $Q_1\cap Q_2=P$. This makes $P$ an ideal of $T$, so $P\subseteq I$ by maximality (a); and $I\subseteq P$ by (b) (else $Q_1=Q_2$). Therefore $P=Q_1\cap Q_2=I$: **minimal splitting occurs exactly at the conductor.**

## Complete Proof

$T\supseteq R$ are commutative domains with common $1$; $I=\{r\in R:\forall t\in T,\ rt\in R\}$; $P$ is prime in $R$; $Q_1,Q_2$ are primes in $T$ with $Q_1\cap R=P=Q_2\cap R$.

### Part (a): $I$ is the largest ideal of $T$ contained in $R$

**$I$ is an ideal of $T$.** $I\subseteq R$ and $0\in I$. For $r,r'\in I$, $t\in T$: $(r-r')t=rt-r't\in R$, so $r-r'\in I$. For $r\in I$, $s\in T$: first $sr=rs\in R$ (take $t=s$ in the definition), and for any $t\in T$, $(sr)t=r(st)\in R$ (as $st\in T$, $r\in I$); so $sr\in I$. Thus $I$ is an ideal of $T$, and $I\subseteq R$.

**Maximality.** If $J\subseteq R$ is an ideal of $T$, then for $r\in J$ and $t\in T$, $rt\in J\subseteq R$, so $r\in I$; hence $J\subseteq I$. $\qquad\checkmark$

### Part (b): $I\not\subseteq P\ \Rightarrow\ Q_1=Q_2$

Pick $x\in I\setminus P$. Since $x\in R$ and $P=Q_j\cap R$, $x\notin P$ gives $x\notin Q_1$ and $x\notin Q_2$. We show $Q_1\subseteq Q_2$; symmetry then gives equality. Let $t\in Q_1$. By the conductor property $xt\in R$, and $xt\in Q_1$ ($Q_1$ an ideal of $T$), so
$$
xt\in Q_1\cap R=P=Q_2\cap R\subseteq Q_2 .
$$
As $Q_2$ is prime and $x\notin Q_2$, $xt\in Q_2$ forces $t\in Q_2$. Hence $Q_1\subseteq Q_2$, and likewise $Q_2\subseteq Q_1$, so $Q_1=Q_2$. $\qquad\checkmark$

### Part (c): for $u\in Q$, $\sum a_iu^i\in Q\cap R[u]\iff a_0\in P$

Let $Q$ be prime in $T$ with $Q\cap R=P$, $u\in Q$, and $\alpha=a_nu^n+\cdots+a_1u+a_0\in R[u]$ ($a_i\in R$). Each higher term $a_iu^i$ ($i\ge 1$) lies in $Q$ (it has the factor $u\in Q$ and $a_i\in R\subseteq T$, $Q$ an ideal of $T$), so
$$
\alpha-a_0=\sum_{i\ge 1}a_iu^i\in Q,\qquad\text{i.e.}\qquad \alpha\equiv a_0\pmod Q .
$$
Therefore $\alpha\in Q\iff a_0\in Q$. Since $a_0\in R$, $a_0\in Q\iff a_0\in Q\cap R=P$. As $\alpha\in R[u]$ already, $\alpha\in Q\cap R[u]\iff a_0\in P$. $\qquad\checkmark$

*(This holds for each chosen representation; if $\alpha$ has two representations with constant terms $a_0,b_0$, both satisfy $a_0\in P\iff\alpha\in Q\iff b_0\in P$, so the criterion is consistent.)*

### Part (d): $u\in Q_1\cap Q_2\ \Rightarrow\ Q_1\cap R[u]=Q_2\cap R[u]$

Since $u\in Q_1$ and $u\in Q_2$, part (c) applies to both primes with the *same* prime $P=Q_1\cap R=Q_2\cap R$. For any $\alpha=\sum a_iu^i\in R[u]$,
$$
\alpha\in Q_1\cap R[u]\iff a_0\in P\iff \alpha\in Q_2\cap R[u].
$$
Thus $Q_1\cap R[u]$ and $Q_2\cap R[u]$ are the same subset of $R[u]$. $\qquad\checkmark$

### Part (e): $Q_1\ne Q_2$, agreeing only on $R$, forces $P=Q_1\cap Q_2=I$

Assume $Q_1\ne Q_2$ and that for every ring $S$ with $R\subseteq S\subseteq T$, $Q_1\cap S=Q_2\cap S$ holds *only* for $S=R$.

**$Q_1\cap Q_2\subseteq R$.** Let $u\in Q_1\cap Q_2$. Then $R[u]$ is a ring with $R\subseteq R[u]\subseteq T$, and by part (d), $Q_1\cap R[u]=Q_2\cap R[u]$. By hypothesis the only such intermediate ring is $R$, so $R[u]=R$, i.e. $u\in R$. As $u$ was arbitrary, $Q_1\cap Q_2\subseteq R$.

**$Q_1\cap Q_2=P$.** Since $Q_1\cap Q_2\subseteq R$,
$$
Q_1\cap Q_2=(Q_1\cap Q_2)\cap R=(Q_1\cap R)\cap(Q_2\cap R)=P\cap P=P .
$$

**$P=I$.** The set $P=Q_1\cap Q_2$ is an ideal of $T$ (intersection of two ideals of $T$) and is contained in $R$; by maximality in part (a), $P\subseteq I$. Conversely, if $I\not\subseteq P$ then part (b) would give $Q_1=Q_2$, contradicting $Q_1\ne Q_2$; hence $I\subseteq P$. Therefore
$$
P=Q_1\cap Q_2=I. \qquad\blacksquare
$$

### Remark — splitting happens at the conductor

The conductor $I$ is the obstruction to $R$ being all of $T$, and these parts show it is precisely the locus of bad behavior for primes. Away from $I$ (part b), a prime $P$ of $R$ has a *unique* prime of $T$ above it — the clean "unramified/inert" situation. The interesting phenomena (a prime of $R$ splitting into several primes of $T$) are confined to primes containing $I$. Part (e) sharpens this to a converse-flavored statement: a *minimally* split pair $Q_1\ne Q_2$ — distinct yet indistinguishable on every proper intermediate ring — can only sit over $P=I$ itself, with $Q_1\cap Q_2=P=I$ an honest ideal of $T$. This is the affine shadow of how primes split in orders inside their integral closures (e.g. $\mathbb{Z}[\sqrt d]\subset\mathcal{O}_K$): away from the conductor the splitting matches the maximal order, and all the irregularities concentrate at the finitely many primes dividing the conductor. (Cf. b90A04, which proves the unique-lifting half in the same conductor framework.)

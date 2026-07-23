<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b90A04: The conductor ideal and unique lifting of primes away from it

## Why It's Hard

This is a six-part tower that quietly develops the theory of the **conductor** $C=\{x\in R:\ xT\subseteq R\}$ of a subring $R$ in a domain $T$, and ends with a real theorem: a prime $P$ of $R$ not containing $C$ has a **unique** prime of $T$ lying over it. The difficulties are cumulative and each rests on the previous parts.

The first subtlety is constant vigilance about **"ideal of $R$" versus "ideal of $T$"** — the conductor is special precisely because it is an ideal of *both*, the largest ideal of $T$ that fits inside $R$ (parts a–c). The asymmetry between $R$-multiplication and $T$-multiplication is where careless arguments break.

The deeper difficulty is parts (d)–(f), where one must build a prime $Q\subseteq T$ out of data living in $R$. The obstruction is that $P$ is only an ideal of $R$, so a product $s\cdot(\text{element of }P)$ with $s\in T$ need *not* land back in $P$. The whole problem hinges on a single trick — **multiply by the conductor element $x$ to descend into $R$** — packaged as the cancellation lemma (d): $xt\in P\iff x^2t\in P$. That lemma is the workhorse that converts unruly $T$-products into $R$-products $(xs)(xt)$, where the conductor guarantees membership in $R$ and the primality of $P$ finally bites.

## The Key Insight

The conductor element $x\in C\setminus P$ is a **bridge from $T$ to $R$**: by definition of $C$, $xt\in R$ for *every* $t\in T$. So multiplying by $x$ drags any element of $T$ into $R$, where $P$ is an honest prime ideal. Two moves recur:

- **Descend:** to test "$t\in T$ relative to $P$," look at $xt\in R$.
- **Cancel (Lemma d):** since $x\notin P$ and $P$ is prime, $x^2t=x\cdot(xt)\in P$ forces $xt\in P$ — one factor of $x$ can be cancelled.

Together they pin down the unique prime over $P$: it *must* be $Q=\{t\in T:\ xt\in P\}$. Closure and primality of $Q$ follow by rewriting $T$-products via $x^2(st)=(xs)(xt)$ — a product of two $R$-elements — and applying primality of $P$; uniqueness follows because any lift $Q'$ contains $xt\in R$ exactly when $t\in Q$.

## Complete Proof

Throughout, $T$ is a commutative domain, $R\subseteq T$ a subring with the same $1$, and $C=\{x\in R:\ \forall t\in T,\ xt\in R\}$.

### Part (a): $C$ is an ideal of $R$

$C\subseteq R$ by definition, and $0\in C$ (as $0\cdot t=0\in R$). For $x,y\in C$ and $t\in T$, $(x-y)t=xt-yt\in R$ (difference of elements of $R$), so $x-y\in C$: an additive subgroup. For $x\in C$, $r\in R$, $t\in T$: $(rx)t=r(xt)$, and $xt\in R$, $r\in R$ give $r(xt)\in R$; hence $rx\in C$. So $C$ is an ideal of $R$. $\qquad\checkmark$

### Part (b): $C$ is an ideal of $T$

We already have the additive subgroup structure. Let $x\in C$ and $s\in T$. First $sx\in R$: taking $t=s$ in the definition gives $xs\in R$, and $sx=xs$ by commutativity. Now for any $t\in T$, $(sx)t=x(st)$ with $st\in T$, so $x(st)\in R$ (since $x\in C$); thus $(sx)t\in R$ for all $t$, i.e. $sx\in C$. So $C$ absorbs multiplication by $T$ and is an ideal of $T$. $\qquad\checkmark$

### Part (c): any ideal $I$ of $R$ that is also an ideal of $T$ satisfies $I\subseteq C$

Let $x\in I$. Then $x\in R$ (as $I\subseteq R$), and for every $t\in T$, $xt\in I$ (since $I$ is an ideal of $T$), hence $xt\in R$ (as $I\subseteq R$). By definition $x\in C$. So $I\subseteq C$. $\qquad\checkmark$

*(Parts a–c say $C$ is the largest ideal of $T$ contained in $R$ — the conductor of $R$ in $T$.)*

### Part (d): for $x\in C\setminus P$ and $t\in T$: $xt\in P\iff x^2t\in P$

(Both $xt$ and $x^2t=x(xt)$ lie in $R$: $xt\in R$ since $x\in C$, and then $x(xt)\in R$ since $x,xt\in R$. So all terms are in $R$, where $P$ is an ideal.)

$(\Rightarrow)$ If $xt\in P$, then $x^2t=x\cdot(xt)\in P$ because $x\in R$ and $P$ is an ideal of $R$.

$(\Leftarrow)$ If $x^2t\in P$, write $x^2t=x\cdot(xt)$ as a product of the two elements $x,\,xt\in R$. Since $P$ is **prime** in $R$, $x\in P$ or $xt\in P$; but $x\notin P$, so $xt\in P$. $\qquad\checkmark$

### Part (e): $Q=\{t\in T:\ xt\in P\}$ is a prime ideal of $T$, and $Q\cap R=P$

**$Q$ is an ideal of $T$.** $0\in Q$. For $t_1,t_2\in Q$, $x(t_1-t_2)=xt_1-xt_2\in P$, so $t_1-t_2\in Q$. For $t\in Q$ and $s\in T$, we must show $st\in Q$, i.e. $x(st)\in P$. By Lemma (d) (applied to $st\in T$) it suffices that $x^2(st)\in P$. Now
$$
x^2(st)=(xs)(xt),
$$
where $xs\in R$ (conductor: $x\in C$, $s\in T$) and $xt\in P$; since $P$ is an ideal of $R$, the product $(xs)(xt)\in P$. Hence $x^2(st)\in P$, so $x(st)\in P$ and $st\in Q$. Thus $Q$ is an ideal of $T$.

**$Q$ is proper.** $1\in Q$ would mean $x=x\cdot1\in P$, contradicting $x\notin P$. So $Q\ne T$.

**$Q$ is prime.** Suppose $st\in Q$, i.e. $x(st)\in P$. By Lemma (d), $x^2(st)\in P$, i.e. $(xs)(xt)\in P$ with $xs,xt\in R$. Primality of $P$ gives $xs\in P$ or $xt\in P$, i.e. $s\in Q$ or $t\in Q$. So $Q$ is prime.

**$Q\cap R=P$.**
- $P\subseteq Q\cap R$: for $p\in P\subseteq R$, $xp\in P$ (as $x\in R$, $P$ an ideal of $R$), so $p\in Q$; and $p\in R$. Hence $p\in Q\cap R$.
- $Q\cap R\subseteq P$: for $r\in Q\cap R$, we have $r\in R$ and $xr\in P$; since $x,r\in R$ and $P$ is prime with $x\notin P$, we get $r\in P$.

Therefore $Q\cap R=P$. $\qquad\blacksquare$ (for (e))

### Part (f): any prime $Q'$ of $T$ with $Q'\cap R=P$ equals $Q$

First note $x\notin Q'$: $x\in R$, so if $x\in Q'$ then $x\in Q'\cap R=P$, contradicting $x\in C\setminus P$.

**$Q\subseteq Q'$.** If $t\in Q$ then $xt\in P=Q'\cap R\subseteq Q'$. Since $Q'$ is prime and $xt\in Q'$, either $x\in Q'$ or $t\in Q'$; as $x\notin Q'$, we get $t\in Q'$.

**$Q'\subseteq Q$.** If $t\in Q'$, then $xt\in Q'$ ($Q'$ an ideal of $T$, $x\in T$). Also $xt\in R$ by the conductor property ($x\in C$). Hence $xt\in Q'\cap R=P$, i.e. $t\in Q$.

Therefore $Q=Q'$. $\qquad\blacksquare$

### Remark — what this theorem says

The conductor $C$ measures the failure of $R$ to be all of $T$ (for an order $R$ in the ring of integers $T=\mathcal{O}_K$ of a number field, $C$ is the classical conductor, and $T/C$, $R/C$ are where $R$ and $T$ differ). Parts (a)–(c) characterize $C$ intrinsically as the largest common ideal. Parts (d)–(f) prove the key arithmetic consequence: **away from the conductor, primes lift uniquely**. Concretely, if a prime $P\subset R$ does not contain $C$, there is exactly one prime $Q\subset T$ with $Q\cap R=P$, and it is computed by the explicit formula $Q=\{t: xt\in P\}$ for any bridge element $x\in C\setminus P$. (At primes containing $C$ — the finitely many "bad" primes dividing the conductor — uniqueness can fail and a prime of $R$ may split into several primes of $T$.) The single engine behind every part is that an element of the conductor multiplies all of $T$ into $R$, letting the primality of $P$ inside $R$ govern the prime structure of the larger ring $T$.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b01J01: How a normal subgroup interacts with primes and Sylow structure

## Why It's Hard

This is a four-part tower in which each part is a tool for the next, and the real challenge is seeing the **two recurring mechanisms** that run through all of them:

1. **Divisibility transfers through the quotient by a normal subgroup** (parts a–b), via the second isomorphism theorem $HK/K\cong H/(H\cap K)$.
2. **The map $P\mapsto P\cap K$ relates the Sylow theory of $G$ and of $K$** (parts c–d), as a surjection of conjugation-$G$-sets.

Each part has a genuine sticking point. Part (a) hinges on noticing that $p\nmid|H\cap K|$ means the full $p$-part of $|H|$ survives in the quotient $H/(H\cap K)$, which embeds in $G/K$. Part (b)'s leap is recognizing that $G'=[G,G]$ is the *right* normal subgroup: it is normal (so (a) applies) **and** $G/G'$ is abelian, which is exactly what upgrades "$p\mid|G/G'|$" into an honest **index-$p$** subgroup — a subtlety, since "$p$ divides the order" does *not* in general give an index-$p$ subgroup (it gives an order-$p$ one, by Cauchy; the two coincide only because of abelianness). Part (c) requires an order computation that secretly uses normality (so that $PK$ is a subgroup), and part (d) needs the insight that the conjugation actions make $P\mapsto P\cap K$ **equivariant between transitive $G$-sets**, forcing all fibers equal.

## The Key Insight

A normal subgroup $K$ "sees" the prime $p$ through intersection, and **$P\mapsto P\cap K$ is the throughline**:

- **(c)** For $P\in Sp(G)$, the subgroup $PK$ (a group because $K\trianglelefteq G$) has $p$-part $p^{v_p|G|}$, and the count $|PK|=|P||K|/|P\cap K|$ forces $|P\cap K|$ to be the *full* $p$-part of $|K|$ — so $P\cap K$ is Sylow in $K$, and every Sylow of $K$ arises this way. Thus $P\mapsto P\cap K$ is a **surjection** $Sp(G)\twoheadrightarrow Sp(K)$.
- **(d)** This surjection is **$G$-equivariant** for the conjugation actions (both transitive, by Sylow), so $G$ permutes its fibers transitively; all fibers have equal size $f$, whence $|Sp(G)|=f\cdot|Sp(K)|$ and $|Sp(K)|\mid|Sp(G)|$.

The earlier parts are the quotient half: $HK/K\cong H/(H\cap K)$ injects the $p$-divisibility of $H$ into $G/K$ (a), and taking $K=G'$ makes the quotient abelian, converting that into an index-$p$ subgroup (b).

## Complete Proof

Throughout, $G$ is finite, $H\le G$, $K\trianglelefteq G$, $G'=[G,G]$, and for a prime $p$ we write $v_p(n)$ for the exponent of $p$ in $n$. Recall $Sp(\,\cdot\,)$ is the *set* of Sylow $p$-subgroups, so $|Sp(\,\cdot\,)|=n_p(\,\cdot\,)$ is their number.

### Part (a): $p\mid|H|$, $p\nmid|H\cap K|$ $\Rightarrow$ $p\mid|G/K|$

Since $K\trianglelefteq G$, the product $HK$ is a subgroup and the **second isomorphism theorem** gives
$$
HK/K\;\cong\;H/(H\cap K),\qquad\text{so}\qquad |HK/K|=\frac{|H|}{|H\cap K|}.
$$
Taking $p$-adic valuations and using $p\mid|H|$ (so $v_p(|H|)\ge1$) and $p\nmid|H\cap K|$ (so $v_p(|H\cap K|)=0$),
$$
v_p\big(|HK/K|\big)=v_p(|H|)-v_p(|H\cap K|)=v_p(|H|)\ge 1,
$$
so $p\mid|HK/K|$. But $HK/K$ is a subgroup of $G/K$, so by Lagrange $|HK/K|$ divides $|G/K|$. Therefore $p\mid|G/K|$. $\qquad\checkmark$

### Part (b): $p\mid|H|$, $p\nmid|H\cap G'|$ $\Rightarrow$ $G$ has a subgroup of index $p$

The commutator subgroup $G'$ is normal in $G$, so part (a) applies with $K=G'$: from $p\mid|H|$ and $p\nmid|H\cap G'|$ we conclude
$$
p\ \big|\ |G/G'|.
$$
Now $G/G'$ is the **abelianization** — a finite *abelian* group whose order is divisible by $p$. By the structure theorem, $G/G'\cong\prod_i\mathbb{Z}/d_i\mathbb{Z}$; since $p$ divides the order, $p\mid d_j$ for some $j$, giving a surjection
$$
G/G'\twoheadrightarrow \mathbb{Z}/d_j\mathbb{Z}\twoheadrightarrow\mathbb{Z}/p\mathbb{Z}.
$$
Its kernel $\overline M\le G/G'$ has index $p$. Let $M$ be the preimage of $\overline M$ under the projection $\pi:G\to G/G'$. Then $M\le G$ and, by the correspondence theorem,
$$
[G:M]=[G/G':\overline M]=p.
$$
So $G$ has a subgroup of index $p$. $\qquad\checkmark$

*(Remark: abelianness of $G/G'$ is essential — it is what makes a quotient of order $p$, hence an index-$p$ subgroup, exist. In a nonabelian group $p\mid|G|$ alone need not yield an index-$p$ subgroup.)*

### Part (c): $Sp(K)=\{P\cap K : P\in Sp(G)\}$

Write $v_p(|G|)=a$ and $v_p(|K|)=b$; Sylow $p$-subgroups of $G$ have order $p^a$ and those of $K$ have order $p^b$.

**Every $P\cap K$ is Sylow in $K$.** Fix $P\in Sp(G)$. Then $P\cap K$ is a $p$-group (subgroup of the $p$-group $P$) contained in $K$. Since $K\trianglelefteq G$, $PK$ is a subgroup of $G$ with
$$
|PK|=\frac{|P|\,|K|}{|P\cap K|},\qquad\text{so}\qquad v_p(|PK|)=a+b-v_p(|P\cap K|).
$$
On the other hand $P\le PK\le G$ forces $p^a=|P|\,\big|\,|PK|\,\big|\,|G|$, and since $v_p(|G|)=a$ this pins $v_p(|PK|)=a$ exactly. Equating, $a+b-v_p(|P\cap K|)=a$, i.e. $v_p(|P\cap K|)=b$. As $P\cap K$ is a $p$-group, $|P\cap K|=p^b$, so $P\cap K\in Sp(K)$.

**Every Sylow of $K$ is some $P\cap K$.** Let $Q\in Sp(K)$, so $|Q|=p^b$. Then $Q$ is a $p$-subgroup of $G$, so by **Sylow's theorem** it lies in some $P\in Sp(G)$: $Q\le P$. Together with $Q\le K$ this gives $Q\le P\cap K$. But $|P\cap K|=p^b=|Q|$ by the previous paragraph, so $Q=P\cap K$.

Combining both directions, $Sp(K)=\{P\cap K : P\in Sp(G)\}$, and in particular $P\mapsto P\cap K$ is a **surjection** $Sp(G)\twoheadrightarrow Sp(K)$. $\qquad\checkmark$

### Part (d): $|Sp(K)|$ divides $|Sp(G)|$

Let $G$ act by conjugation on both $Sp(G)$ and $Sp(K)$. These actions are well-defined and **transitive**:

- On $Sp(G)$: Sylow's theorem says all Sylow $p$-subgroups of $G$ are conjugate in $G$.
- On $Sp(K)$: for $g\in G$ and $Q\in Sp(K)$, $gQg^{-1}$ is a Sylow $p$-subgroup of $gKg^{-1}=K$ (normality of $K$), so it lies in $Sp(K)$; and the Sylow $p$-subgroups of $K$ are already conjugate *within* $K\le G$, hence $G$ acts transitively.

The map $\Phi:Sp(G)\to Sp(K)$, $\Phi(P)=P\cap K$, is **$G$-equivariant**: using $gKg^{-1}=K$,
$$
\Phi(gPg^{-1})=gPg^{-1}\cap K=gPg^{-1}\cap gKg^{-1}=g(P\cap K)g^{-1}=g\,\Phi(P)\,g^{-1}.
$$
By part (c), $\Phi$ is surjective. Now I claim **all fibers of $\Phi$ have the same size.** Given $Q,Q'\in Sp(K)$, transitivity provides $g\in G$ with $gQg^{-1}=Q'$; equivariance then shows $P\mapsto gPg^{-1}$ maps $\Phi^{-1}(Q)$ bijectively onto $\Phi^{-1}(Q')$ (if $\Phi(P)=Q$ then $\Phi(gPg^{-1})=gQg^{-1}=Q'$, and conjugation by $g^{-1}$ is the inverse). Hence every fiber has a common cardinality $f$, and counting $Sp(G)$ fiber-by-fiber over the surjection,
$$
|Sp(G)|=f\cdot|Sp(K)|.
$$
Therefore $|Sp(K)|$ divides $|Sp(G)|$. $\qquad\blacksquare$

### Remark — the architecture

The four parts split cleanly into the two mechanisms named at the top. Parts (a)–(b) are *quotient* statements: the bridge $HK/K\cong H/(H\cap K)$ pushes the prime $p$ from $H$ into $G/K$, and specializing $K=G'$ exploits the universal property of the commutator subgroup ($G/G'$ is the largest abelian quotient) to realize $p$ as the index of an actual subgroup. Parts (c)–(d) are *Sylow* statements built on the single natural map $P\mapsto P\cap K$: normality of $K$ makes $PK$ a group (forcing $P\cap K$ to capture the full $p$-part of $K$) and makes the conjugation actions compatible (forcing equal fibers). The slogan: **a normal subgroup is transparent to $p$ both upward (its quotient) and downward (its Sylows), and the same intersection/product bookkeeping governs both.** The divisibility $n_p(K)\mid n_p(G)$ in (d) is the quantitative shadow of the qualitative fact in (c) that Sylows of $K$ are exactly the traces of Sylows of $G$.

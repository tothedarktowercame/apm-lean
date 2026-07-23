<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b98J01: Groups of order 36 are semidirect products of their Sylow subgroups

## Why It's Hard

This is a guided classification of groups of order $36=2^2\cdot 3^2$, and the difficulty is that five Sylow- and structure-theoretic ideas must be chained in exactly the right order, each feeding the next. The spine is the **conjugation action on the four Sylow $3$-subgroups**, which embeds a quotient of $G$ into $S_4$; pinning down its kernel (order $3$, not $9$) and image (the unique order-$12$ subgroup $A_4$) is the delicate first step, and the hypothesis "no normal subgroup of order $9$" is used precisely to force the kernel to be small.

The genuinely clever capstone is **part (e)**, which must produce a fact *incompatible with $|Z(N)|=2$*. (The printed "$Z(N)<G$" is trivially true and cannot be the intended statement; the content that makes the concluding remark work is that the order-$3$ subgroup $K$ is **central** — $K\subseteq Z(N)$, equivalently $C_G(K)=G$.) The proof of that centrality is a slick centralizer count whose punchline is the recurring fact **"$A_4$ has no subgroup of order $6$"**: a centralizer of index $2$ would manufacture exactly such a forbidden subgroup. With $K$ central, $|Z(N)|\ge 3\ne 2$, so part (d) forces $N$ abelian, its Sylow $2$-subgroup becomes normal in $G$, and $G$ splits as a semidirect product of Sylows.

## The Key Insight

There are $n_3=4$ Sylow $3$-subgroups (each self-normalizing, since $|N_G(P_3)|=36/4=9=|P_3|$), so $G$ acts on them, giving $\varphi:G\to S_4$. The image is transitive of order dividing $\gcd(36,24)=12$ and divisible by $4$, so $12$; the kernel $K=\bigcap_g gP_3g^{-1}$ has order $3$ (order $9$ would be a normal Sylow $3$, excluded). Thus
$$
G/K\cong A_4\quad(\text{the only order-12 subgroup of }S_4).
$$
Pulling back the Klein four normal subgroup $V\trianglelefteq A_4$ gives a normal $N\trianglelefteq G$ of order $12$ containing $K$, with $N\cong \mathbb{Z}/3\rtimes V_4$. Its center is all of $N$ (trivial action) or exactly order $2$ (nontrivial action). The decisive point: **$K$ is central in $G$**, because $C_G(K)$ cannot have index $2$ (that would give $A_4$ a subgroup of order $6$). So $3\mid|Z(N)|$, ruling out $|Z(N)|=2$, forcing $N$ abelian — and then the Sylow $2$-subgroup of $N$ is normal in $G$, so $G$ is a semidirect product of its Sylow subgroups.

## Complete Proof

Let $|G|=36=2^2\cdot 3^2$. Sylow's theorems give $n_3\in\{1,4\}$ and $n_2\in\{1,3,9\}$; Sylow $3$-subgroups have order $9$, Sylow $2$-subgroups order $4$.

### Part (a): no normal order-9 subgroup $\Rightarrow$ $K\trianglelefteq G$ of order 3 with $G/K\cong A_4$

"No normal subgroup of order $9$" means the Sylow $3$-subgroup is not normal, so $n_3\ne 1$, hence $n_3=4$. Let $G$ act by conjugation on the set of four Sylow $3$-subgroups; this gives a homomorphism $\varphi:G\to S_4$ with image transitive (Sylow's conjugacy theorem). Let $K=\ker\varphi$.

The image $G/K$ embeds in $S_4$, so $|G/K|$ divides $\gcd(|G|,|S_4|)=\gcd(36,24)=12$; transitivity forces $4\mid|G/K|$, leaving $|G/K|\in\{4,12\}$ and $|K|\in\{9,3\}$. Now each Sylow $3$-subgroup $P$ is self-normalizing ($|N_G(P)|=|G|/n_3=9=|P|$), so $K=\bigcap_g gN_G(P)g^{-1}=\bigcap_g gPg^{-1}\subseteq P$; thus $|K|\mid 9$. If $|K|=9$ then $K=P$ would be a normal Sylow $3$-subgroup — excluded by hypothesis. Hence $|K|=3$, $|G/K|=12$, and $K\trianglelefteq G$.

Finally $G/K$ is a transitive subgroup of $S_4$ of order $12$, and the only order-$12$ subgroup of $S_4$ is $A_4$, so $G/K\cong A_4$. $\qquad\checkmark$

### Part (b): $A_4$ has a normal subgroup of order 4

The Klein four-group $V=\{e,(12)(34),(13)(24),(14)(23)\}$ is a union of conjugacy classes of $A_4$ (the identity together with all three products of two disjoint transpositions), hence closed under conjugation: $V\trianglelefteq A_4$, with $|V|=4$. $\qquad\checkmark$

### Part (c): $G$ has a normal subgroup $N$ of order 12 containing $K$

By (b), $V\trianglelefteq A_4\cong G/K$. Under the correspondence theorem, $V=N/K$ for a unique subgroup $N$ with $K\subseteq N\subseteq G$, and $N\trianglelefteq G$ because $N/K\trianglelefteq G/K$. Then $|N|=|N/K|\cdot|K|=4\cdot 3=12$. $\qquad\checkmark$

### Part (d): $N$ is abelian, or $|Z(N)|=2$

$N$ has order $12$ and contains $K$ (order $3$), which is normal in $G$ hence in $N$; as $K$ has order $3$ and $N/K\cong V_4$ has order $4$, $K$ is the unique (normal) Sylow $3$-subgroup of $N$. Letting $Q$ be a Sylow $2$-subgroup of $N$ (order $4$), $K\cap Q=\{e\}$ and $KQ=N$, so $N=K\rtimes_\theta Q$ with $Q\cong N/K\cong V_4$ and action $\theta:Q\to\operatorname{Aut}(K)\cong\mathbb{Z}/2$.

- If $\theta$ is trivial, $N=K\times Q\cong\mathbb{Z}/3\times V_4$ is **abelian**.
- If $\theta$ is nontrivial, write $K=\langle a\rangle$. An element $a^iq$ ($q\in Q$) is central iff it commutes with $a$ and with $Q$. Commuting with $a$ forces $q\in\ker\theta$ (only those $q$ centralize $a$); commuting with every $w\in Q$ forces $a^i=\theta(w)(a^i)$, and for $w\notin\ker\theta$ this gives $a^i=a^{-i}$, i.e. $a^{2i}=e$, i.e. $i\equiv 0\pmod 3$, so $a^i=e$. Hence $Z(N)=\ker\theta$, which has order $|Q|/|\mathrm{im}\,\theta|=4/2=2$. So $|Z(N)|=2$. $\qquad\checkmark$

### Part (e): $K\subseteq Z(N)$ (so $|Z(N)|\ne 2$), hence $N$ is abelian

Since $K\trianglelefteq G$ with $|K|=3$, conjugation gives $G\to\operatorname{Aut}(K)\cong\mathbb{Z}/2$ with kernel $C_G(K)$, so $[G:C_G(K)]\in\{1,2\}$.

Suppose $[G:C_G(K)]=2$. Then $|C_G(K)|=18$, and $C_G(K)\supseteq K$ (as $K$ is abelian), so its image $C_G(K)/K$ is a subgroup of $G/K\cong A_4$ of order $18/3=6$. But **$A_4$ has no subgroup of order $6$** (an index-$2$ subgroup would be normal and contain all eight $3$-cycles as squares, impossible in a group of order $6$). Contradiction.

Therefore $[G:C_G(K)]=1$, i.e. $C_G(K)=G$: the subgroup $K$ is central in $G$, so in particular $K\subseteq Z(N)$. Hence $3=|K|$ divides $|Z(N)|$, so $|Z(N)|\ge 3$, which is **incompatible with $|Z(N)|=2$**. By part (d), the only remaining possibility is that $N$ is **abelian**. $\qquad\blacksquare$

### Remark — the semidirect-product conclusion

Combining everything: in the case where $G$ has no normal Sylow $3$-subgroup, parts (a)–(e) force the order-$12$ normal subgroup $N$ to be abelian. Then the Sylow $2$-subgroup of $N$ (a $V_4$, unique because $N$ is abelian) is characteristic in $N$, hence normal in $G$ (as $N\trianglelefteq G$). So $G$ has a normal Sylow $2$-subgroup $P_2$, and with a Sylow $3$-subgroup $P_3$ satisfying $P_2\cap P_3=\{e\}$, $P_2P_3=G$, we get $G=P_2\rtimes P_3$. In the complementary case (a normal Sylow $3$-subgroup exists), $G=P_3\rtimes P_2$ directly. Either way, **every group of order $36$ is a semidirect product of its Sylow subgroups**. The argument is a model of how Sylow counting, the action on Sylow subgroups, and the rigidity of $A_4$ (no order-$6$ subgroup) combine to pin down group structure; the same "$A_4$ has no subgroup of order $6$" fact recurs throughout finite group theory (cf. b93J01).

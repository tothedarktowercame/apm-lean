<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b99A02: Structure of groups of order 5075 = 5²·7·29 via a Sylow cascade

## Why It's Hard

This is a guided Sylow analysis of groups of order $5075=5^2\cdot 7\cdot 29$, and the difficulty is orchestration: each part sets up the next, and the deductions must be made in the right order using a recurring but easy-to-miss principle — **a unique Sylow subgroup of a normal subgroup is characteristic in it, hence normal in the whole group**. The naive approach (try to show each Sylow normal directly by counting) fails for the Sylow $29$- and $7$-subgroups, whose counts are not pinned to $1$ by the global arithmetic alone.

The trick is to *change the ambient group*: pass to the quotient $G/P$ (order $7\cdot 29$) to find a normal Sylow $29$, pull it back, and then work *inside* the resulting normal subgroup $H$ where the Sylow $29$ becomes unique. The final part (e) is the cleanest payoff: the only Sylow not forced to be normal is the Sylow $7$-subgroup $R$, and $K=PR$ is normal exactly when $R$ is — which happens exactly when all three Sylows are normal, i.e. when $G$ is the direct product of its (automatically abelian) Sylow subgroups, i.e. when $G$ is abelian.

## The Key Insight

The arithmetic forces a chain of normal subgroups. With $|G|=5^2\cdot 7\cdot 29$:

- **$P$ (order $25$) is normal:** $n_5\mid 7\cdot 29=203$ and $n_5\equiv 1\pmod 5$, and among the divisors $1,7,29,203$ only $1$ is $\equiv 1\pmod 5$.
- **Move to $G/P$** (order $7\cdot 29=203$): there $n_{29}\mid 7$, $\equiv 1\pmod{29}$ forces $n_{29}=1$, a normal Sylow $29$; pull back to $H\trianglelefteq G$ of order $5^2\cdot 29$.
- **Inside $H$**, $n_{29}\mid 25$, $\equiv 1\pmod{29}$ forces $n_{29}=1$, so the Sylow $29$ subgroup $Q$ is unique in $H$, hence characteristic in $H$, hence **normal in $G$**.

So $P,Q\trianglelefteq G$, and $K=PR$ (order $5^2\cdot 7$) exists because $P$ is normal. The lone undetermined Sylow is $R$ (order $7$): $K$ is normal $\iff$ $R$ is normal (it is characteristic in $K$) $\iff$ all of $P,Q,R$ are normal $\iff$ $G=P\times Q\times R$ — and each factor (orders $5^2$, $7$, $29$) is abelian, so this holds $\iff$ $G$ is abelian.

## Complete Proof

Let $|G|=5075=5^2\cdot 7\cdot 29$, with Sylow subgroups $P$ (order $25$), $R$ (order $7$), $Q$ (order $29$).

### Part (a): $P$ is normal

By Sylow, $n_5\equiv 1\pmod 5$ and $n_5\mid 7\cdot 29=203$. The divisors of $203$ are $1,7,29,203$, with residues $1,2,4,3\pmod 5$ respectively; only $1\equiv 1$. Hence $n_5=1$, so $P$ is the unique Sylow $5$-subgroup and $P\trianglelefteq G$. $\qquad\checkmark$

### Part (b): $G$ has a normal subgroup $H$ of order $5^2\cdot 29$

Since $P\trianglelefteq G$, form $G/P$, of order $5075/25=203=7\cdot 29$. In $G/P$, the number of Sylow $29$-subgroups satisfies $\bar n_{29}\equiv 1\pmod{29}$ and $\bar n_{29}\mid 7$; as $7\not\equiv 1\pmod{29}$, we get $\bar n_{29}=1$, so $G/P$ has a normal Sylow $29$-subgroup $\bar Q$ (order $29$). Its preimage $H$ under $G\to G/P$ is a subgroup with $H/P=\bar Q$, and $H\trianglelefteq G$ because $\bar Q\trianglelefteq G/P$ (preimages of normal subgroups are normal). Then
$$
|H|=|H/P|\cdot|P|=29\cdot 25=5^2\cdot 29. \qquad\checkmark
$$

### Part (c): $Q$ is normal

First, $Q\subseteq H$. Indeed $H$ (order $5^2\cdot 29$) contains a Sylow $29$-subgroup of $G$; any Sylow $29$-subgroup $Q$ of $G$ is conjugate to it, $Q=gQ_0g^{-1}$, and since $H\trianglelefteq G$, $Q=gQ_0g^{-1}\subseteq gHg^{-1}=H$. (A normal subgroup containing one Sylow $p$-subgroup contains all of them.)

Now count Sylow $29$-subgroups *within* $H$: $n_{29}(H)\equiv 1\pmod{29}$ and $n_{29}(H)\mid 25$; the divisors $1,5,25$ have residues $1,5,25\pmod{29}$, so only $1$ works, giving $n_{29}(H)=1$. Thus $Q$ is the unique Sylow $29$-subgroup of $H$, hence **characteristic** in $H$ (any automorphism permutes Sylow subgroups, fixing the unique one). Since $Q$ is characteristic in $H$ and $H\trianglelefteq G$, we conclude $Q\trianglelefteq G$. $\qquad\checkmark$

### Part (d): $G$ has a subgroup $K$ of order $5^2\cdot 7$

Since $P\trianglelefteq G$, the product $K:=PR$ is a subgroup, and as $\gcd(|P|,|R|)=\gcd(25,7)=1$ gives $P\cap R=\{e\}$,
$$
|K|=\frac{|P|\,|R|}{|P\cap R|}=\frac{25\cdot 7}{1}=5^2\cdot 7. \qquad\checkmark
$$

### Part (e): $K$ is normal $\iff$ $G$ is abelian

**($\Leftarrow$)** If $G$ is abelian, every subgroup is normal, so $K\trianglelefteq G$.

**($\Rightarrow$)** Suppose $K=PR\trianglelefteq G$. Inside $K$ (order $5^2\cdot 7$), count Sylow $7$-subgroups: $n_7(K)\equiv 1\pmod 7$ and $n_7(K)\mid 25$; the divisors $1,5,25$ have residues $1,5,4\pmod 7$, so $n_7(K)=1$. Hence $R$ is the unique Sylow $7$-subgroup of $K$, so $R$ is characteristic in $K$; as $K\trianglelefteq G$, this gives $R\trianglelefteq G$.

Now $P,Q,R$ are all normal in $G$, with pairwise coprime orders $25,29,7$, so pairwise trivial intersections, and more generally $P\cap QR=\{e\}$, $Q\cap PR=\{e\}$, $R\cap PQ=\{e\}$ (coprime orders). Since $|P|\,|Q|\,|R|=25\cdot 29\cdot 7=5075=|G|$, the standard internal-direct-product criterion gives
$$
G=P\times Q\times R.
$$
Each factor is abelian: $|Q|=29$ and $|R|=7$ are primes (cyclic), and $|P|=5^2$ is a prime square (every group of order $p^2$ is abelian). A direct product of abelian groups is abelian, so $G$ is abelian. $\qquad\blacksquare$

### Remark — the cascade and the abelian dichotomy

The proof is a model Sylow cascade: normality propagates from $P$ (forced by counting) through the quotient $G/P$ to a normal $H$, and then *down* into $H$ to make $Q$ normal — the key recurring move being "unique Sylow $\Rightarrow$ characteristic $\Rightarrow$ normal in the ambient group when housed in a normal subgroup." After (a)–(d), the entire indeterminacy of $G$ is concentrated in the Sylow $7$-subgroup $R$: whether or not it is normal. Part (e) shows this single bit decides everything — $R$ normal forces $G=P\times Q\times R$, a product of abelian Sylows, hence abelian; and conversely. The cleanest summary: among groups of order $5^2\cdot 7\cdot 29$, the Sylow $5$- and $29$-subgroups are *always* normal, and the group is abelian iff the Sylow $7$-subgroup is normal too. The one way to be nonabelian is for $R$ to act nontrivially on $Q$: this is possible precisely because $7\mid 28=29-1=|\mathrm{Aut}(\mathbb{Z}/29)|$, giving the nonabelian Frobenius group $Q\rtimes R$ of order $203$ and hence the nonabelian $G\cong P\times(Q\rtimes R)$ with $R$ (and $K=PR$) not normal. (By contrast $R$ cannot act nontrivially on $P$, since $7\nmid|\mathrm{Aut}(\mathbb{Z}/25)|=20$ and $7\nmid|GL_2(\mathbb{F}_5)|=480$.) So the abelian-vs-nonabelian dichotomy is governed entirely by the single divisibility $7\mid 29-1$.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b97J01: p-groups have nontrivial center and are nilpotent

## Why It's Hard

Parts (a)–(b) are definitional, but the examples must be chosen so their *defining series* are easy to compute: a non-solvable group needs a constant derived series (simplicity does this), and a solvable-not-nilpotent group needs a terminating derived series but a stalling lower central series (trivial center does this). The real mathematics is (c)–(d), and the difficulty is recognizing that **one tool — the class equation — drives both, recursively**.

Part (c) is not obvious a priori: why should a $p$-group have *any* element commuting with everything? The class equation reveals it by a divisibility argument — every non-central conjugacy class has size divisible by $p$, so the center must absorb the leftover divisibility. Part (d) then has the subtlety that you cannot read nilpotency off $G$ directly; you must **iterate (c) through quotients**: $G/Z(G)$ is again a $p$-group with nontrivial center, and so on up the upper central series. Seeing that center-nontriviality is simultaneously the base case *and* the inductive engine is the crux.

## The Key Insight

The **class equation**
$$
|G|=|Z(G)|+\sum_i [G:C_G(x_i)]
$$
(sum over representatives of the non-central conjugacy classes) has every term $[G:C_G(x_i)]$ a divisor of $|G|=p^n$ that is $>1$, hence divisible by $p$. Since $p\mid|G|$, we get $p\mid|Z(G)|$, forcing $|Z(G)|\ge p>1$ — a **nontrivial center** (c).

This self-propagates. $G/Z(G)$ is a smaller $p$-group, so it too has nontrivial center, so the **upper central series**
$$
\{e\}=Z_0\subsetneq Z_1\subsetneq Z_2\subsetneq\cdots,\qquad Z_{i+1}/Z_i=Z(G/Z_i),
$$
strictly increases (by (c) applied to each nontrivial $G/Z_i$) until it reaches $G$ — which is exactly nilpotency (d). Center-nontriviality is the base case and the climbing mechanism at once.

## Complete Proof

### Part (a): definitions

For a group $G$:
- **Solvable:** the *derived series* $G^{(0)}=G$, $G^{(i+1)}=[G^{(i)},G^{(i)}]$ reaches $\{e\}$, i.e. $G^{(n)}=\{e\}$ for some $n$. (Equivalently, $G$ has a subnormal chain with abelian quotients.)
- **Nilpotent:** the *lower central series* $\gamma_1=G$, $\gamma_{i+1}=[\gamma_i,G]$ reaches $\{e\}$; equivalently the *upper central series* $Z_0=\{e\}$, $Z_{i+1}/Z_i=Z(G/Z_i)$ reaches $G$. (Equivalently, $G$ has a subnormal chain with *central* quotients.)

Nilpotent $\Rightarrow$ solvable (a central series is in particular abelian-quotient), but not conversely.

### Part (b): examples

**Not solvable: $A_5$ (or $S_5$).** $A_5$ is simple and nonabelian, so its commutator subgroup $[A_5,A_5]$ — a normal subgroup — is either $\{e\}$ or $A_5$; it is not $\{e\}$ (that would make $A_5$ abelian), so $[A_5,A_5]=A_5$. Hence the derived series is constant: $A_5^{(i)}=A_5\ne\{e\}$ for all $i$, and $A_5$ is not solvable.

**Solvable but not nilpotent: $S_3$.** Derived series $S_3\trianglerighteq[S_3,S_3]=A_3\trianglerighteq\{e\}$ (with $A_3\cong\mathbb{Z}/3$ abelian), so $S_3^{(2)}=\{e\}$: solvable. But $Z(S_3)=\{e\}$ while $S_3\ne\{e\}$; a nontrivial nilpotent group has nontrivial center (its upper central series starts $Z_1=Z(G)$ and cannot climb from $\{e\}$), so $S_3$ is not nilpotent. (Equivalently $\gamma_2(S_3)=A_3$, $\gamma_3(S_3)=[A_3,S_3]=A_3$, and the lower central series stalls at $A_3$.)

### Part (c): a group of order $p^n>1$ has nontrivial center

Let $|G|=p^n$ with $n\ge 1$. Let $G$ act on itself by conjugation; the orbits are the conjugacy classes, and an element $x$ has a singleton class iff $x\in Z(G)$. Choosing representatives $x_1,\dots,x_r$ of the conjugacy classes of size $>1$, the orbit–stabilizer theorem gives $|\text{class of }x_i|=[G:C_G(x_i)]$, and the **class equation** is
$$
p^n=|G|=|Z(G)|+\sum_{i=1}^{r}[G:C_G(x_i)].
$$
For each $i$, the class has size $>1$, so $C_G(x_i)\ne G$, and $[G:C_G(x_i)]$ is a divisor of $p^n$ greater than $1$ — hence divisible by $p$. Also $p\mid p^n=|G|$. Therefore
$$
|Z(G)|=|G|-\sum_i[G:C_G(x_i)]\equiv 0\pmod p,
$$
so $p\mid|Z(G)|$. Since $e\in Z(G)$ gives $|Z(G)|\ge 1$, divisibility by $p$ forces $|Z(G)|\ge p>1$. Thus $Z(G)$ is nontrivial. $\qquad\blacksquare$

### Part (d): a finite group of prime-power order is nilpotent

Let $|G|=p^n$. Consider the upper central series $Z_0=\{e\}$, $Z_{i+1}/Z_i=Z(G/Z_i)$ (well-defined: $Z_i\trianglelefteq G$ inductively, and the preimage of the center of $G/Z_i$ is a normal subgroup $Z_{i+1}\supseteq Z_i$).

**Claim:** as long as $Z_i\ne G$, the inclusion $Z_i\subsetneq Z_{i+1}$ is strict. Indeed, if $Z_i\ne G$ then $G/Z_i$ is a nontrivial group of order $p^{\,n}/|Z_i|$ — a prime power $>1$ — so by part (c) its center $Z(G/Z_i)=Z_{i+1}/Z_i$ is nontrivial, i.e. $Z_{i+1}\supsetneq Z_i$.

Thus $\{e\}=Z_0\subsetneq Z_1\subsetneq Z_2\subsetneq\cdots$ is a strictly increasing chain of subgroups of the finite group $G$, so it cannot increase forever: it stabilizes, and by the Claim it can only stabilize once it reaches $G$. Hence $Z_m=G$ for some $m$. An upper central series reaching $G$ is precisely the definition of nilpotency, so $G$ is nilpotent (of class $\le m$). $\qquad\blacksquare$

*(Alternative by induction on $n$: $G/Z(G)$ has smaller prime-power order, hence is nilpotent by induction with $\gamma_{m+1}(G/Z(G))=\{e\}$; this gives $\gamma_{m+1}(G)\subseteq Z(G)$, so $\gamma_{m+2}(G)=[\gamma_{m+1}(G),G]\subseteq[Z(G),G]=\{e\}$, and $G$ is nilpotent.)*

### Remark — the architecture and what it buys

Part (c) is the load-bearing fact, and (d) is just (c) applied repeatedly up the quotient tower; together they show **every finite $p$-group is nilpotent**, a cornerstone of finite group theory. This in turn underlies the structure theorem that *a finite group is nilpotent iff it is the direct product of its Sylow subgroups* (each a $p$-group, hence nilpotent), iff all its Sylow subgroups are normal. The examples in (b) calibrate the hierarchy abelian $\subsetneq$ nilpotent $\subsetneq$ solvable $\subsetneq$ all groups: $S_3$ separates nilpotent from solvable, and $A_5$ separates solvable from the rest. The class equation's divisibility argument — "non-central orbits are all divisible by $p$, so the fixed points (center) inherit the divisibility" — is the same counting principle behind Cauchy's theorem and the Sylow theorems.

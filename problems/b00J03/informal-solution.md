<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b00J03: For a nonabelian group of order p³, Z(G) = [G,G] has order p

## Why It's Hard

There are two assertions — $|Z(G)|=p$ and $Z(G)=[G,G]$ — and they are entangled: you cannot identify the commutator subgroup with the center until you have already pinned the center down. The difficulty is orchestrating several standard $p$-group facts in the right order and recognizing that the **single hypothesis "nonabelian" must be spent twice**, in two different roles.

Pinning $|Z(G)|=p$ is a squeeze from both sides. The lower bound is the well-known fact that a $p$-group has nontrivial center (class equation). The upper bound is the trap: the only subtle exclusion is $|Z(G)|=p^2$, which one rules out *not* directly but via the deceptively strong lemma "**if $G/Z(G)$ is cyclic then $G$ is abelian**." Forgetting that lemma, or trying to exclude $p^2$ by hand, is where the proof usually stalls.

Identifying $Z(G)=[G,G]$ then rests on two containments that meet exactly because the center has order $p$ — a prime, the atomic case. One inclusion comes from "$G/Z(G)$ has order $p^2$, hence is abelian, hence $[G,G]\subseteq Z(G)$"; the reverse comes from "$G$ nonabelian forces $[G,G]\ne 1$." Containment of a *nontrivial* subgroup inside a subgroup of *prime* order forces equality — there is no room in between.

## The Key Insight

A group of order $p$ has **no proper nontrivial subgroups** (Lagrange). So once we know $|Z(G)|=p$, any subgroup of $Z(G)$ is either trivial or all of $Z(G)$. The whole identification $Z(G)=[G,G]$ then reduces to two soft facts:

- $G/Z(G)$ has order $p^2$ ⟹ abelian ⟹ $[G,G]\subseteq Z(G)$ (commutators die in an abelian quotient);
- $G$ nonabelian ⟹ $[G,G]\ne\{e\}$.

A nontrivial subgroup sitting inside a group of prime order *is* that group: $[G,G]=Z(G)$. The hypothesis "nonabelian" is the lever used both to keep $Z(G)$ small (via the $G/Z$-cyclic lemma) and to keep $[G,G]$ nonzero — the same scarcity argument, applied twice.

## Complete Proof

Let $G$ be nonabelian with $|G|=p^3$, $p$ prime. Write $Z=Z(G)$ for the center and $[G,G]$ for the commutator (derived) subgroup.

### Lemmas used

- **(L1) Nontrivial center.** Every finite $p$-group $G\ne\{e\}$ has $Z(G)\ne\{e\}$. *(Class equation: $|G|=|Z(G)|+\sum_i [G:C_G(x_i)]$, summed over noncentral conjugacy-class representatives. Each index $[G:C_G(x_i)]$ is a power of $p$ greater than $1$, so $p$ divides $|G|$ and the sum; hence $p\mid |Z(G)|$.)*
- **(L2) $G/Z$ cyclic ⟹ abelian.** If $G/Z(G)$ is cyclic, then $G$ is abelian. *(Write $G/Z=\langle gZ\rangle$. Every element of $G$ has the form $g^{a}z$ with $z\in Z$; two such, $g^{a}z$ and $g^{b}w$, commute because powers of $g$ commute with each other and $z,w$ are central.)*
- **(L3) $[G,G]\subseteq N \iff G/N$ abelian**, for $N\trianglelefteq G$. *(The quotient $G/N$ is abelian iff every commutator lies in $N$; equivalently $[G,G]$ is the smallest normal subgroup with abelian quotient.)*

### Step 1 — $|Z|=p$

By Lagrange $|Z|\in\{1,p,p^2,p^3\}$. By **(L1)**, $|Z|\ne 1$. Rule out the two large cases:

- If $|Z|=p^3$ then $Z=G$, i.e. $G$ is abelian — contradiction.
- If $|Z|=p^2$ then $|G/Z|=p^3/p^2=p$, so $G/Z$ is cyclic (any group of prime order is cyclic). By **(L2)**, $G$ is abelian — contradiction.

The only surviving possibility is
$$
|Z(G)|=p .
$$

### Step 2 — $G/Z$ is abelian

By Step 1, $|G/Z|=p^3/p=p^2$. **Every group of order $p^2$ is abelian:** its center is nontrivial by (L1), and if the center had order $p$ the quotient by it would be cyclic of order $p$, forcing the group abelian by (L2) — contradicting that its center is proper; hence the center is the whole group. Therefore $G/Z$ is abelian.

### Step 3 — $[G,G]\subseteq Z$

Since $G/Z$ is abelian (Step 2) and $Z\trianglelefteq G$, **(L3)** gives
$$
[G,G]\subseteq Z .
$$
In particular $|[G,G]|$ divides $|Z|=p$, so $|[G,G]|\in\{1,p\}$.

### Step 4 — $[G,G]\ne\{e\}$, hence $[G,G]=Z$

If $[G,G]=\{e\}$, then every commutator $xyx^{-1}y^{-1}=e$, i.e. $xy=yx$ for all $x,y$, so $G$ is abelian — contradiction. Hence $[G,G]\ne\{e\}$, so by Step 3, $|[G,G]|=p=|Z|$. A subgroup of $Z$ (a group of order $p$) with the same order $p$ must equal $Z$. Therefore
$$
\boxed{\,Z(G)=[G,G]\quad\text{and}\quad |Z(G)|=p.\,}\qquad\blacksquare
$$

### Remark — the structural picture

The proof exhibits the canonical shape of a nonabelian $p^3$ group: a central subgroup $Z\cong\mathbb{Z}/p$ that *is simultaneously* the commutator subgroup, with abelian quotient $G/Z\cong(\mathbb{Z}/p)^2$. Equivalently, the lower central series is $G\trianglerighteq [G,G]=Z\trianglerighteq\{e\}$, so $G$ is nilpotent of class exactly $2$ ("just barely nonabelian"). This is realized concretely by the two nonabelian groups of order $p^3$: the **Heisenberg group** of unipotent upper-triangular $3\times3$ matrices over $\mathbb{F}_p$ (exponent $p$ for $p$ odd) and, for instance, $\mathbb{Z}/p^2\rtimes\mathbb{Z}/p$ — in both, the center, the commutator subgroup, and the set of $p$-th-power/Frobenius data all collapse onto the same order-$p$ subgroup. The engine of the whole argument is the rigidity of prime order: nontrivial $+$ contained-in-order-$p$ $=$ equal.

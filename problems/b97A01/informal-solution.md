<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b97A01: The structure of S₄, and order-24 groups with a non-normal Sylow 3-subgroup

## Why It's Hard

Part (a) is a careful census — conjugacy classes by cycle type, then assembling them into
the (few) normal subgroups, then a solvable chain. Part (b) is the elegant heart: from the
single hypothesis "Sylow $3$ not normal" you must extract a *map to $S_4$* (the
conjugation action on the four Sylow $3$-subgroups), and then pin its kernel to order
exactly $2$ — too small would make $G\cong S_4$, and any factor of $3$ in the kernel is
impossible. That forces $G/K\cong A_4$, and the normal Sylow $2$ of $A_4$ pulls back to a
normal Sylow $2$ of $G$. Part (c) requires recognizing the canonical non-split double
cover, $SL(2,3)$.

## The Key Insight

- **(a)** Conjugacy classes of $S_4$ are the cycle types; the only unions that are
  subgroups (hence the normal subgroups) are $\{e\}\subset V_4\subset A_4\subset S_4$,
  with quotients $V_4,\ \mathbb{Z}/3,\ \mathbb{Z}/2$ — all abelian, so $S_4$ is solvable.
- **(b)** $n_3\in\{1,4\}$; not normal $\Rightarrow n_3=4$. Conjugation on the $4$ Sylow
  $3$'s gives $\varphi:G\to S_4$. Its kernel $K$ can't be divisible by $3$ (else $K\supseteq$
  all four Sylow $3$'s, too big) and can't be trivial (else $G\cong S_4$), so $|K|=2$,
  $G/K\cong A_4$; pulling back $V_4\trianglelefteq A_4$ gives a normal Sylow $2$.
- **(c)** $SL(2,3)$: order $24$, center $\{\pm I\}\cong\mathbb{Z}/2$, quotient $A_4$,
  Sylow $2=Q_8$ normal, Sylow $3$ not normal — and $\not\cong S_4$ (nontrivial center).

## Complete Proof

### (a) Conjugacy classes, normal subgroups, solvability of $S_4$

Two permutations are conjugate in $S_n$ iff they have the same cycle type, so the
conjugacy classes of $S_4$ are indexed by partitions of $4$:

| cycle type | representative | size |
|---|---|---|
| $1+1+1+1$ | $e$ | $1$ |
| $2+1+1$ | $(1\,2)$ | $6$ |
| $2+2$ | $(1\,2)(3\,4)$ | $3$ |
| $3+1$ | $(1\,2\,3)$ | $8$ |
| $4$ | $(1\,2\,3\,4)$ | $6$ |

(Sizes sum to $1+6+3+8+6=24=|S_4|$.)

**Normal subgroups.** A normal subgroup is a union of conjugacy classes containing $e$,
of order dividing $24$. Scanning sums $1+(\text{subset of }\{6,3,8,6\})$ that both divide
$24$ and form a subgroup: $1$ gives $\{e\}$; $1+3=4$ gives $V_4=\{e,(12)(34),(13)(24),
(14)(23)\}$ (the Klein four-group); $1+3+8=12$ gives $A_4$ (the even permutations); and
$24$ gives $S_4$. No other class-union has admissible order (e.g. $1+6,\,1+8,\,1+3+6$ give
$7,9,10$). Hence the normal subgroups are exactly
$$
\{e\}\ \subset\ V_4\ \subset\ A_4\ \subset\ S_4 .
$$

**Solvability.** This same chain is a subnormal series with abelian quotients:
$$
S_4/A_4\cong\mathbb{Z}/2,\quad A_4/V_4\cong\mathbb{Z}/3,\quad V_4/\{e\}\cong\mathbb{Z}/2\times\mathbb{Z}/2,
$$
each abelian ($V_4\trianglelefteq A_4$ since $V_4\trianglelefteq S_4$). A group with a
subnormal series of abelian quotients is solvable, so $S_4$ is solvable. $\quad\checkmark$

### (b) Order-24, not $S_4$, Sylow 3 not normal

Let $|G|=24=2^3\cdot3$. The number of Sylow $3$-subgroups satisfies $n_3\equiv1\pmod3$
and $n_3\mid 8$, so $n_3\in\{1,4\}$. Since the Sylow $3$ is not normal, $n_3=4$.

**The map to $S_4$.** Let $G$ act by conjugation on the set $X$ of its $4$ Sylow
$3$-subgroups, giving a homomorphism
$$
\varphi:G\to \operatorname{Sym}(X)\cong S_4 .
$$
Let $K=\ker\varphi=\bigcap_{P\in X}N_G(P)$. The action is transitive (Sylow), so $4$
divides $|\varphi(G)|=24/|K|$.

**$|K|=2$.** First, $3\nmid|K|$: if $3\mid|K|$ then the normal subgroup $K$ contains a
subgroup $Q$ of order $3$, which is a Sylow $3$-subgroup of $G$; normality of $K$ forces
all four conjugate Sylow $3$'s into $K$, contributing $4\cdot2=8$ elements of order $3$,
so $|K|\ge9$ — impossible since $|K|$ divides $|N_G(P)|=24/4=6$. So $|K|\in\{1,2\}$. If
$|K|=1$, $\varphi$ is injective and $|G|=24=|S_4|$ forces $\varphi$ to be an isomorphism
$G\cong S_4$, contrary to hypothesis. Hence
$$
|K|=2 .
$$
Then $|\varphi(G)|=24/2=12$, and the only subgroup of $S_4$ of order $12$ is $A_4$, so
$\varphi(G)=A_4$ and $G/K\cong A_4$.

**The Sylow $2$-subgroup is normal.** Since $K$ has order $2$, it is central: conjugation
permutes the single non-identity element of $K$ to itself, so that element is central.
Being a central $2$-element, it lies in *every* Sylow $2$-subgroup; thus $K\subseteq S$
for any Sylow $2$-subgroup $S$ (order $8$). In $G/K\cong A_4$, the image $SK/K\cong
S/(S\cap K)=S/K$ has order $8/2=4$ — a Sylow $2$-subgroup of $A_4$, namely $V_4$, which is
**normal** in $A_4$. The preimage of a normal subgroup is normal, so
$$
\varphi^{-1}(V_4)\trianglelefteq G,\qquad |\varphi^{-1}(V_4)|=|V_4|\cdot|K|=4\cdot2=8 .
$$
Thus $\varphi^{-1}(V_4)$ is a normal subgroup of order $8$, i.e. *the* (unique) Sylow
$2$-subgroup of $G$ is normal. $\quad\blacksquare$

### (c) An explicit example: $SL(2,3)=SL_2(\mathbb{F}_3)$

Take $G=SL_2(\mathbb{F}_3)$, the $2\times2$ matrices of determinant $1$ over
$\mathbb{F}_3$. Its order is $|SL_2(\mathbb{F}_3)|=3(3^2-1)=24$.

- **$G\not\cong S_4$:** the center of $G$ is $\{\pm I\}\cong\mathbb{Z}/2$ (note $-I\neq I$
  since $\operatorname{char}=3$), whereas $Z(S_4)=\{e\}$. So they are non-isomorphic.
- **Sylow $3$ not normal:** a Sylow $3$-subgroup is generated by a transvection, e.g.
  $\begin{psmallmatrix}1&1\\0&1\end{psmallmatrix}$ (order $3$); these are not all equal,
  and in fact $n_3=4$ (conjugates by the action on the $4$ points of
  $\mathbb{P}^1(\mathbb{F}_3)$), so the Sylow $3$ is not normal.
- It matches (b): $G/\{\pm I\}=PSL_2(\mathbb{F}_3)\cong A_4$, the central $K=\{\pm I\}$
  has order $2$, and the Sylow $2$-subgroup is the quaternion group $Q_8$, which is
  normal in $G$.

So $SL_2(\mathbb{F}_3)$ is a group of exactly the type in (b). $\quad\blacksquare$

### Remark

Part (b) classifies these groups as the non-split central extensions $1\to\mathbb{Z}/2\to
G\to A_4\to1$: the action $\varphi$ realizes $G/Z\cong A_4$ with $Z=K$ of order $2$, and
$SL_2(\mathbb{F}_3)$ is the canonical one (the binary tetrahedral group, $Q_8\rtimes
\mathbb{Z}/3$). The contrast with $S_4$ is instructive: $S_4$ also surjects onto
$S_3\cong S_4/V_4$ and has the same order, but its Sylow $3$-normalizer setup gives an
*injective* $\varphi$ (kernel $1$), whereas the hypothesis "$G\not\cong S_4$" is exactly
what pushes the kernel up to order $2$ and makes the Sylow $2$ normal.

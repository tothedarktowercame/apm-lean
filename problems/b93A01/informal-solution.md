<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b93A01: Order-pq groups and their minimal faithful permutation degree

## Why It's Hard

The first half is standard order-$pq$ structure theory (Sylow $\Rightarrow$ normal
$C_q$; two normal Sylows $\Rightarrow$ direct product). The interesting half is the
**degree** questions: not just *can* $G$ act faithfully on $n$ letters, but the
*smallest* such $n$. These need two different optima for the two structures —
nonabelian $G$ has minimal degree $q$ (acting on the cosets of the non-normal Sylow
$p$), while cyclic $G=C_{pq}$ has minimal degree $p+q$ (disjoint $p$- and $q$-cycles).
The non-embedding directions are the crux: you must show $S_{q-1}$ and $S_{p+q-1}$
genuinely lack the needed elements, via divisibility of $|S_n|$ and a cycle-length
count.

## The Key Insight

- **(a)** $n_q\mid p$, $n_q\equiv1\,(q)$ and $p<q$ force $n_q=1$: a normal $C_q$. If
  also a normal $C_p$, then $G=C_p\times C_q\cong C_{pq}$ — abelian.
- **(b)** Nonabelian $\Rightarrow$ the Sylow $p$-subgroup $P$ is *not* normal (else (a)
  makes $G$ abelian), so the action on the $q$ cosets $G/P$ is faithful: $G\hookrightarrow
  S_q$. And $q\mid|G|$ but $q\nmid (q-1)!$, so $G\not\hookrightarrow S_{q-1}$.
- **(c)** Abelian $\Rightarrow G\cong C_{pq}$; a $p$-cycle times a disjoint $q$-cycle
  has order $pq$ on $p+q$ letters. Conversely any order-$pq$ permutation needs a
  $p$-divisible cycle ($\ge p$) and a $q$-divisible cycle ($\ge q$), so $\ge p+q$ moved
  points — none exist in $S_{p+q-1}$.

## Complete Proof

Let $|G|=pq$, $p<q$ prime.

### Part (a)

**A normal subgroup of order $q$.** By Sylow, the number $n_q$ of Sylow
$q$-subgroups satisfies $n_q\equiv1\pmod q$ and $n_q\mid p$. The divisors of $p$ are
$1,p$, and $p\not\equiv1\pmod q$ (since $1<p<q$). Hence $n_q=1$: the Sylow
$q$-subgroup $Q$ is normal, $|Q|=q$.

**If also a normal subgroup of order $p$.** Suppose $P\trianglelefteq G$ with $|P|=p$.
Then $P\cap Q=\{e\}$ (orders $p,q$ are coprime) and $|PQ|=pq=|G|$, so $G=PQ$. With both
$P,Q$ normal and meeting trivially, $G$ is the internal direct product
$$
G\cong P\times Q\cong C_p\times C_q\cong C_{pq},
$$
which is abelian (indeed cyclic, as $\gcd(p,q)=1$). $\quad\checkmark$

### Part (b): $G$ nonabelian

Let $P$ be a Sylow $p$-subgroup, $|P|=p$, so $[G:P]=q$. Let $G$ act on the set of $q$
left cosets $G/P$ by left multiplication, giving $\varphi:G\to
\operatorname{Sym}(G/P)\cong S_q$, with kernel $K=\ker\varphi=\bigcap_{g}gPg^{-1}
\subseteq P$.

$K$ is normal in $G$ and contained in $P$, so $|K|\mid p$, i.e. $K=\{e\}$ or $K=P$. If
$K=P$ then $P=\bigcap gPg^{-1}\trianglelefteq G$; combined with the normal $Q$ from (a),
part (a) would make $G$ abelian — contrary to hypothesis. Hence $K=\{e\}$ and
$\varphi$ is injective:
$$
G\hookrightarrow S_q. \quad\checkmark
$$

**$G\not\hookrightarrow S_{q-1}$.** If $G$ were isomorphic to a subgroup of $S_{q-1}$,
Lagrange would give $|G|=pq\ \big|\ |S_{q-1}|=(q-1)!$. In particular $q\mid (q-1)!$.
But $q$ is prime and every factor in $(q-1)!=1\cdot2\cdots(q-1)$ is strictly less than
$q$, hence not divisible by $q$; so $q\nmid(q-1)!$. This contradiction shows $G$ is not
isomorphic to a subgroup of $S_{q-1}$. $\quad\checkmark$

### Part (c): $G$ abelian

An abelian group of order $pq$ with distinct primes is cyclic: by (a) (or the
classification of finite abelian groups) $G\cong C_p\times C_q\cong C_{pq}$. Fix a
generator $g$ of order $pq$.

**$G\hookrightarrow S_{p+q}$.** On a set of $p+q$ letters partitioned into a block of
$p$ and a disjoint block of $q$, let
$$
\sigma=\underbrace{(1\,2\,\cdots\,p)}_{p\text{-cycle}}\ \underbrace{(p{+}1\ \cdots\ p{+}q)}_{q\text{-cycle}} .
$$
These cycles are disjoint, so $\operatorname{ord}(\sigma)=\operatorname{lcm}(p,q)=pq$
(as $p\neq q$ are prime). Thus $\langle\sigma\rangle\cong C_{pq}\cong G$, giving an
embedding $G\hookrightarrow S_{p+q}$ (send $g\mapsto\sigma$). $\quad\checkmark$

**$G\not\hookrightarrow S_{p+q-1}$.** An embedding $C_{pq}\hookrightarrow S_n$ sends a
generator to an element of order $pq$, so it suffices to show $S_{p+q-1}$ has **no**
element of order $pq$. Let $\tau\in S_n$ have order $pq$, with disjoint-cycle lengths
$\ell_1,\dots,\ell_r$ (each $\ge 2$), so $\operatorname{lcm}(\ell_1,\dots,\ell_r)=pq$.
Since $p\mid\operatorname{lcm}$, some $\ell_i$ is divisible by $p$, hence $\ell_i\ge p$;
since $q\mid\operatorname{lcm}$, some $\ell_j$ is divisible by $q$, hence $\ell_j\ge q$.
- If $i=j$, that cycle length is divisible by both $p$ and $q$, hence by $pq$, so
  $\ell_i\ge pq\ge p+q$ (because $pq-(p+q)=(p-1)(q-1)-1\ge 1\cdot2-1=1>0$).
- If $i\ne j$, the two cycles are disjoint, so $\tau$ moves at least $\ell_i+\ell_j\ge
  p+q$ points.

Either way $\tau$ moves at least $p+q$ points, so it lives only in $S_n$ with $n\ge
p+q$. Thus $S_{p+q-1}$ contains no element of order $pq$, and $G\cong C_{pq}$ is not
isomorphic to a subgroup of $S_{p+q-1}$. $\quad\blacksquare$

### Remark

The two non-embedding bounds are *sharp* and compute the **minimal faithful
permutation degree** $\mu(G)$: $\mu(G)=q$ for the nonabelian $C_q\rtimes C_p$ (it acts
faithfully and transitively on the $q$ cosets of $P$, and can't fit in $S_{q-1}$), and
$\mu(C_{pq})=p+q$ (disjoint cycles are forced because a single $pq$-cycle would waste
$pq>p+q$ points). The contrast is the whole point: a nonabelian group can be "more
efficient" as permutations because a non-normal subgroup gives a small faithful coset
action, whereas a cyclic group must spend one orbit per prime.

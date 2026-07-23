<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM b03J01: Smallest-prime-index subgroups are normal; groups of twin-prime order p(p+2) are cyclic

## Why It's Hard

**Part (a)** is the classic "index = smallest prime $\Rightarrow$ normal" theorem. The
familiar index-$2$ case is easy (the two cosets force left = right cosets), but index
$p$ has no such shortcut: $H$ can be huge and is not a Sylow subgroup. The only handle
is the action of $G$ on the $p$ cosets, landing $G$ in $S_p$, after which a divisibility
**squeeze** that secretly uses minimality of $p$ collapses $H$ onto a normal kernel.

**Part (b)** must turn an arithmetic coincidence — that $p$ and $p+2$ are *twin
primes* — into a unique group structure. Order $pq$ with $p<q$ is the smallest
nontrivial classification, and it hinges on whether $p \mid q-1$. The twin-prime gap
$q-1=p+1$ is *just barely* not a multiple of $p$, and that single fact forces both
Sylow subgroups to be normal, splitting $G$ as a direct product.

## The Key Insight

**(a)** $G$ acts on $G/H$ ($p$ cosets) $\Rightarrow \varphi:G\to S_p$ with
$\ker\varphi=\operatorname{core}(H)\subseteq H$. Then $[G:\ker\varphi]$ divides both
$|G|$ and $p!$; any prime factor is $\ge p$ (minimality) and $\le p$ (divides $p!$),
so it is $p$, and since $p^2\nmid p!$ the index is exactly $p$. With
$\ker\varphi\subseteq H$ of index $p$, this gives $H=\ker\varphi\trianglelefteq G$.

**(b)** With $|G|=pq$, $q=p+2$ (so $p\ge 3$, both odd primes): the Sylow $q$-subgroup
has index $p=$ smallest prime, so it is normal *by part (a)*; the Sylow $p$-subgroup is
normal because $n_p=q$ would require $p\mid q-1=p+1$, i.e. $p\mid 1$ — impossible.
Two normal Sylow subgroups of coprime prime orders give
$G\cong C_p\times C_q\cong C_{p(p+2)}$.

## Complete Proof

### Part (a): a subgroup of index = smallest prime divisor is normal

Let $p$ be the smallest prime dividing $|G|$ and $[G:H]=p$. Let $G$ act on the set $X$
of $p$ left cosets of $H$ by left multiplication, giving $\varphi:G\to
\operatorname{Sym}(X)\cong S_p$ with kernel $K=\ker\varphi$. A $g\in K$ fixes the coset
$H$, so $gH=H$ and $g\in H$; thus $K\subseteq H$, and $K\trianglelefteq G$ as a kernel.

By the first isomorphism theorem $G/K\hookrightarrow S_p$, so $[G:K]$ divides
$p!=|S_p|$; it also divides $|G|$. Let $q$ be any prime dividing $[G:K]$. Then $q\mid
|G|$ forces $q\ge p$ (minimality of $p$), while $q\mid p!$ forces $q\le p$; hence
$q=p$. So $[G:K]$ is a power of $p$, and since $p^2\nmid p!$ (only one multiple of $p$
lies in $\{1,\dots,p\}$), in fact $[G:K]=p$. From $K\subseteq H$ and
$$[G:K]=[G:H][H:K]=p\,[H:K]=p$$
we get $[H:K]=1$, i.e. $H=K\trianglelefteq G$. $\quad\checkmark$

### Part (b): if $p+2$ is prime and $|G|=p(p+2)$, then $G$ is cyclic

Write $q=p+2$, so $|G|=pq$ with $p,q$ both prime. Since $p+2$ is prime we must have
$p\neq 2$ (else $p+2=4$ is not prime), so $p\ge 3$ and $p<q$; in particular $p$ is the
smallest prime dividing $|G|$.

**The Sylow $q$-subgroup is normal.** A Sylow $q$-subgroup $Q$ has order $q$, hence
index $[G:Q]=p$, the smallest prime dividing $|G|$. By **part (a)**, $Q\trianglelefteq
G$. (Equivalently, Sylow gives $n_q\equiv 1\pmod q$ and $n_q\mid p$; as $p<q$ the only
possibility is $n_q=1$.) Being of prime order, $Q\cong C_q$.

**The Sylow $p$-subgroup is normal.** Let $P$ be a Sylow $p$-subgroup, $|P|=p$. By
Sylow, $n_p\equiv 1\pmod p$ and $n_p\mid q$, so $n_p\in\{1,q\}$. If $n_p=q$ then
$q\equiv 1\pmod p$, i.e. $p\mid q-1=(p+2)-1=p+1$, i.e. $p\mid 1$ — impossible for
$p\ge 3$. Hence $n_p=1$ and $P\trianglelefteq G$, with $P\cong C_p$.

**$G$ is the direct product.** Now $P,Q\trianglelefteq G$ with $|P\cap Q|$ dividing
$\gcd(p,q)=1$, so $P\cap Q=\{e\}$; and $|PQ|=|P||Q|=pq=|G|$, so $G=PQ$. A group that is
the internal product of two normal subgroups meeting trivially is their (internal)
direct product:
$$
G \cong P\times Q \cong C_p\times C_q \cong C_{pq}=C_{p(p+2)},
$$
the last step because $\gcd(p,q)=1$ makes $C_p\times C_q$ cyclic. Therefore $G$ is
cyclic. $\quad\blacksquare$

### Remark

Part (b) is the general fact "$|G|=pq$ with $p<q$ and $p\nmid q-1$ $\Rightarrow$ $G$
cyclic," specialized to the twin-prime case where $q-1=p+1$ misses being a multiple of
$p$ by exactly $1$. When $p\mid q-1$ instead (e.g. $|G|=6=2\cdot 3$, $2\mid 2$), the
nonabelian semidirect product appears ($S_3$); the twin-prime hypothesis is precisely
what rules that out. Part (a) is the lever that delivers the normal Sylow $q$ "for
free" at index $p$.

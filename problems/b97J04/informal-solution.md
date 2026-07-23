<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b97J04: The Jordan–Chevalley decomposition, additive and multiplicative

## Why It's Hard

This is the full **Jordan–Chevalley decomposition**: over an algebraically closed field every operator splits uniquely as *commuting* semisimple $+$ nilpotent (additive), and every invertible operator as semisimple $\times$ unipotent (multiplicative). Existence (a) is the generalized-eigenspace construction, but the genuinely subtle part is **uniqueness (c)**, where one must prove that the semisimple part is *forced* — not merely one valid choice among many. The trap is thinking $S$ could be chosen differently; the theorem is that *any* commuting semisimple-plus-nilpotent splitting recovers the same $S$.

The mechanism is a coincidence of two decompositions of $V$: the eigenspace decomposition of the (unknown) $S$ and the generalized-eigenspace decomposition of the (given) $T$. Showing $V_\lambda=W_\lambda$ requires one easy inclusion (on $V_\lambda$, the operator $T-\lambda$ *is* the nilpotent $N$) and one dimension count (both families direct-sum to all of $V$). Part (d) then has its own subtlety: one must see that invertibility of $T$ makes the additive $S$ invertible (same characteristic polynomial), so dividing by $S$ converts the additive decomposition into the multiplicative one, and uniqueness is inherited from (c).

## The Key Insight

Over an algebraically closed field the **generalized eigenspaces**
$$
W_\lambda=\{v:(T-\lambda)^k v=0\text{ for some }k\}=\ker(T-\lambda)^{\dim V}
$$
depend only on $T$ and satisfy $V=\bigoplus_\lambda W_\lambda$ (primary decomposition, since $\chi_T$ splits). The semisimple part is forced to be **"scalar $\lambda$ on $W_\lambda$"**: for *any* commuting splitting $T=S+N$, the $S$-eigenspace $V_\lambda=\ker(S-\lambda)$ equals $W_\lambda$, because

- on $V_\lambda$ one has $T-\lambda=(S-\lambda)+N=N$ (nilpotent), so $V_\lambda\subseteq W_\lambda$;
- both $\{V_\lambda\}$ and $\{W_\lambda\}$ direct-sum to $V$, so the inclusions are equalities by dimension.

Thus $S$ (hence $N=T-S$) is determined by $T$ alone. The multiplicative version is the additive one *divided by $S$*: $U=S^{-1}T=I+S^{-1}N$ is unipotent because $S^{-1}N$ is nilpotent.

## Complete Proof

$F$ is algebraically closed, $V$ finite-dimensional, $T\in\operatorname{End}_F(V)$. Since $F$ is algebraically closed, $\chi_T(x)=\prod_{i=1}^r(x-\lambda_i)^{m_i}$ with distinct $\lambda_i$.

### Part (a): existence of $T=S+N$

By the **primary decomposition theorem** (Cayley–Hamilton plus coprimality of the factors $(x-\lambda_i)^{m_i}$), $V$ is the direct sum of the generalized eigenspaces
$$
V=\bigoplus_{i=1}^r W_i,\qquad W_i=\ker(T-\lambda_i I)^{m_i},
$$
each $T$-invariant. Define $S$ by $S|_{W_i}=\lambda_i I$ (scalar on each block) and set $N=T-S$. Then:

- **$S$ is semisimple:** any basis of $V$ adapted to $\bigoplus W_i$ consists of $S$-eigenvectors, so $S$ is diagonalizable.
- **$N$ is nilpotent:** on $W_i$, $N=T-\lambda_i I$, and $(T-\lambda_i I)^{m_i}=0$ there by definition of $W_i$; taking $k=\max_i m_i$ gives $N^k=0$ on all of $V$.
- **$SN=NS$:** $S,N$ both preserve each $W_i$, and on $W_i$ the scalar $S=\lambda_i I$ commutes with $N|_{W_i}$; commuting blockwise on a direct sum gives $SN=NS$.

Hence $T=S+N$ is a commuting semisimple-plus-nilpotent decomposition. $\qquad\checkmark$

### Part (b): $S$ and $T$ have the same characteristic polynomial

On $W_i$, $T-\lambda_i I=N|_{W_i}$ is nilpotent, so $\lambda_i$ is the only eigenvalue of $T|_{W_i}$ and $\chi_{T|_{W_i}}=(x-\lambda_i)^{\dim W_i}$. Since the characteristic polynomial of a direct sum is the product, $\chi_T=\prod_i(x-\lambda_i)^{\dim W_i}$; comparing with $\chi_T=\prod_i(x-\lambda_i)^{m_i}$ (distinct $\lambda_i$) gives $\dim W_i=m_i$. Now $S=\lambda_i I$ on $W_i$ (dimension $m_i$), so
$$
\chi_S=\prod_i(x-\lambda_i)^{\dim W_i}=\prod_i(x-\lambda_i)^{m_i}=\chi_T. \qquad\checkmark
$$
*(Equivalently: $S$ and $N$ commute, so over the algebraically closed $F$ they are simultaneously triangularizable with $N$ strictly upper-triangular; then $T=S+N$ and $S$ have the same diagonal, hence the same characteristic polynomial.)*

### Part (c): uniqueness

Let $T=S+N$ be *any* decomposition with $S$ semisimple, $N$ nilpotent, $SN=NS$. Put $V_\lambda=\ker(S-\lambda I)$ and $W_\lambda=\{v:(T-\lambda)^kv=0,\ \exists k>0\}$.

**(i) $V_\lambda\subseteq W_\lambda$.** Since $S,N$ commute, $N$ preserves each $S$-eigenspace: $v\in V_\lambda\Rightarrow S(Nv)=N(Sv)=\lambda Nv\Rightarrow Nv\in V_\lambda$. On $V_\lambda$, $T-\lambda I=(S-\lambda I)+N=N$ (as $S=\lambda$ there), so for $v\in V_\lambda$ and $k$ the nilpotency index of $N$, $(T-\lambda)^k v=N^k v=0$. Thus $v\in W_\lambda$.

**(ii) $V_\lambda\supseteq W_\lambda$.** Two facts give two direct-sum decompositions of $V$:
- $V=\bigoplus_\lambda V_\lambda$, because $S$ is semisimple (diagonalizable), so $V$ is the direct sum of its $S$-eigenspaces;
- $V=\bigoplus_\lambda W_\lambda$, the generalized-eigenspace (primary) decomposition of $T$, valid since $\chi_T$ splits over the algebraically closed $F$.

By (i), $V_\lambda\subseteq W_\lambda$, so $\dim V_\lambda\le\dim W_\lambda$ for every $\lambda$. But $\sum_\lambda\dim V_\lambda=\dim V=\sum_\lambda\dim W_\lambda$, so equality must hold termwise: $\dim V_\lambda=\dim W_\lambda$, and with $V_\lambda\subseteq W_\lambda$ this forces $V_\lambda=W_\lambda$.

**Uniqueness.** The spaces $W_\lambda$ are defined purely in terms of $T$, hence independent of the chosen decomposition. Since $V_\lambda=W_\lambda$, the $S$-eigenspaces are determined by $T$; and $S$ is the operator acting as the scalar $\lambda$ on each $W_\lambda$ (with $V=\bigoplus W_\lambda$), so $S$ is uniquely determined by $T$. Then $N=T-S$ is too. $\qquad\blacksquare$

### Part (d): multiplicative decomposition $T=SU$ for $T\in GL(V)$

**Existence.** Take the additive decomposition $T=S+N$ of part (a). By part (b), $\chi_S=\chi_T$; since $T$ is invertible, $0$ is not an eigenvalue of $T$, hence not of $S$, so $S\in GL(V)$. Define
$$
U=S^{-1}T=S^{-1}(S+N)=I+S^{-1}N.
$$
Because $S$ commutes with $N$, so does $S^{-1}$, giving $(S^{-1}N)^k=S^{-k}N^k=0$ for $k$ the nilpotency index of $N$; thus $S^{-1}N$ is nilpotent and $U=I+(\text{nilpotent})$ is **unipotent** (in particular invertible). Then $T=SU$, $S$ is semisimple, $U$ unipotent, and
$$
US=(I+S^{-1}N)S=S+S^{-1}NS=S+N=T=SU,
$$
using $NS=SN$. So $SU=US$.

**Uniqueness.** Suppose $T=S'U'$ with $S'$ semisimple, $U'=I+N'$ unipotent ($N'$ nilpotent), $S'U'=U'S'$ (hence $S'N'=N'S'$), all invertible. Then
$$
T=S'(I+N')=S'+S'N',
$$
and $S'N'$ is nilpotent ($(S'N')^k=S'^kN'^k=0$) and commutes with $S'$ ($S'(S'N')=(S'N')S'$ since $N'$ commutes with $S'$). So $T=S'+S'N'$ is a commuting semisimple-plus-nilpotent decomposition; by the **uniqueness in part (c)**, $S'=S$ and $S'N'=N$. Hence $N'=S'^{-1}N=S^{-1}N$ and $U'=I+N'=I+S^{-1}N=U$. Thus $(S',U')=(S,U)$. $\qquad\blacksquare$

### Remark — one decomposition, two forms

The additive Jordan–Chevalley decomposition $T=S+N$ is the coordinate-free form of Jordan canonical form: $S$ records the eigenvalues (the diagonal), $N$ the off-diagonal nilpotent part, and they commute precisely because both respect the generalized-eigenspace block structure. The content of uniqueness (c) is that *the blocks are intrinsic to $T$* — $W_\lambda=\ker(T-\lambda)^{\dim V}$ — so there is no freedom in $S$. The multiplicative form $T=SU$ is obtained by factoring out $S$, legitimate exactly when $T$ (equivalently $S$) is invertible; it is the linear-algebra shadow of the decomposition of an element of an algebraic group into its semisimple and unipotent parts, central to the structure theory of linear algebraic groups. A useful refinement (provable via the same generalized-eigenspace ideas, the "result on the syllabus") is that $S$ and $N$ are in fact *polynomials in $T$* with no constant term — which makes the commutation $SN=NS$ automatic and shows $S,N$ commute with everything that commutes with $T$.

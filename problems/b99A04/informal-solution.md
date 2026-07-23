<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b99A04: M_n(F) is semisimple — V = Fⁿ is its only simple module and every f.d. module is Vᵐ

## Why It's Hard

The four parts build, from bare hands, the entire representation theory of the matrix ring $R=M_n(F)$ — the simplest noncommutative ring — culminating in a baby case of the **Artin–Wedderburn theorem**: $R$ has (up to isomorphism) a *unique* simple module $V=F^n$, and *every* finite-dimensional $R$-module is a direct sum of copies of $V$. The difficulty is that each step is a small instance of a deep structural idea, and they must be assembled in order:

- **(a)** simplicity of $V$ — the action is "as transitive as possible";
- **(b)** decomposing the ring itself into module copies of $V$ (the *columns*);
- **(c)** a Schur-type rigidity: a nonzero image of a simple module is again that simple module;
- **(d)** semisimplicity: a sum of simple submodules is a *direct* sum, extracted using finite-dimensionality.

The recurring conceptual hurdle is keeping straight that $R$ acts on three different things — $V$, itself (as left ideals), and an abstract module $W$ — and that the *same* simple object $V$ governs all of them. The cleverness in (a) is the rank-one matrix $\frac{1}{v_j}\,w\,e_j^{\!\top}$ that sends a given nonzero vector to any target; in (c)–(d) it is the realization that "image of simple is $0$ or simple" plus "the identity splits as $\sum E_{ii}$" force every module to be a sum, hence direct sum, of $V$'s.

## The Key Insight

$M_n(F)$ moves a single nonzero vector $v$ anywhere: the rank-one matrix $A=\frac{1}{v_j}\,w\,e_j^{\!\top}$ (where $v_j\ne 0$) satisfies $Av=w$. So $Rv=V$ for every $v\ne 0$ — **$V$ is simple** (a). Cutting $R$ into its columns,
$$
R=\bigoplus_{i=1}^n L_i,\qquad L_i=RE_{ii}=\{\text{matrices supported on column }i\}\cong V,
$$
exhibits the ring as $n$ copies of $V$ (b). Consequently, for any module $W$ and $x\in W$, the map $L_i\to L_ix$, $a\mapsto ax$, is a nonzero (when $L_ix\ne 0$) image of the *simple* $L_i\cong V$, hence an isomorphism by Schur: $L_ix\cong V$ (c). Finally the identity $I=\sum_i E_{ii}$ gives $w=Iw=\sum_i E_{ii}w$, so $W=\sum_{x,i}L_ix$ is a **sum of copies of $V$**; finite-dimensionality lets us prune to a direct sum, $W\cong V^m$ (d). One simple module, everything semisimple — Artin–Wedderburn for $M_n(F)$.

## Complete Proof

Let $R=M_n(F)$, $V=F^n$ (column vectors), $E_{ij}$ the matrix units, $e_i$ the standard basis vectors (so $E_{ij}e_k=\delta_{jk}e_i$ and $e_j^{\!\top}v=v_j$).

### Part (a): the only submodules of $V$ are $\{0\}$ and $V$

Let $U\subseteq V$ be a submodule with $U\ne\{0\}$, and pick $0\ne v\in U$; say $v_j\ne 0$. For any target $w\in V$, the matrix $A=\frac{1}{v_j}\,w\,e_j^{\!\top}\in R$ (a rank-one matrix) satisfies
$$
Av=\frac{1}{v_j}\,w\,(e_j^{\!\top}v)=\frac{1}{v_j}\,w\,v_j=w .
$$
Hence $w\in Rv$ for every $w$, i.e. $Rv=V$. Since $U$ is a submodule containing $v$, $V=Rv\subseteq U\subseteq V$, so $U=V$. Thus $V$ is simple. $\qquad\checkmark$

### Part (b): $R=\bigoplus_i L_i$ with each $L_i\cong V$

Let $L_i=RE_{ii}$, the set of matrices whose only (possibly) nonzero column is the $i$-th. Each $L_i$ is a **left ideal**: for $B\in R$ and $A\in L_i$, $(BA)e_k=B(Ae_k)=0$ for $k\ne i$, so $BA\in L_i$.

**Direct sum.** Every $A\in R$ is the sum of its "single-column" pieces $A^{(i)}:=AE_{ii}\in L_i$ (the matrix with $A$'s $i$-th column and zeros elsewhere), so $R=\sum_i L_i$; and $L_i\cap\sum_{k\ne i}L_k=\{0\}$ since the column supports are disjoint. Hence $R=\bigoplus_{i=1}^n L_i$ as left $R$-modules.

**$L_i\cong V$.** Define $\phi_i:L_i\to V$ by $\phi_i(A)=Ae_i$ (the $i$-th column). It is $R$-linear: $\phi_i(BA)=(BA)e_i=B(Ae_i)=B\phi_i(A)$. It is injective (a matrix in $L_i$ is determined by its $i$-th column) and surjective (given $v\in V$, the matrix $v\,e_i^{\!\top}\in L_i$ maps to $v$). So $\phi_i$ is an isomorphism, $L_i\cong V$. $\qquad\checkmark$

### Part (c): if $Lx\ne\{0\}$ then $Lx$ is a submodule $\cong V$

Let $W$ be a left $R$-module, $x\in W$, and $L=L_i$. The set $Lx=\{ax:a\in L\}$ is a submodule of $W$: it is closed under addition, and for $r\in R$, $r(ax)=(ra)x$ with $ra\in L$ (left ideal), so $r(ax)\in Lx$.

Consider the map $\psi:L\to W$, $\psi(a)=ax$; it is $R$-linear with image $Lx$. Its kernel is a submodule of $L\cong V$, which is simple (a), so $\ker\psi\in\{0,L\}$. If $\ker\psi=L$ then $Lx=\psi(L)=\{0\}$, contrary to hypothesis. Hence $\ker\psi=\{0\}$, so $\psi$ is injective and
$$
L\xrightarrow{\ \sim\ }Lx,\qquad\text{thus}\qquad Lx\cong L\cong V. \qquad\checkmark
$$

### Part (d): if $\dim_F W<\infty$ then $W\cong V^m$

Since $I=\sum_{i=1}^n E_{ii}\in R$, every $w\in W$ satisfies $w=Iw=\sum_i E_{ii}w\in\sum_i L_i w$ (as $E_{ii}\in L_i$). Therefore
$$
W=\sum_{w\in W}\ \sum_{i=1}^n L_i w,
$$
a sum of submodules each of which, by part (c), is either $\{0\}$ or isomorphic to $V$. Discard the zero ones; $W$ is a sum of simple submodules each $\cong V$.

Now use $\dim_F W<\infty$ to extract a direct sum. Among all submodules of $W$ expressible as a (finite) direct sum $\bigoplus_k L_{i_k}w_k$ of these simple pieces, choose one $U$ of **maximal $F$-dimension** (possible since dimensions are bounded by $\dim_F W$). Claim $U=W$: if not, some simple piece $L_i w$ is not contained in $U$ (the pieces generate $W$). Then $L_iw\cap U$ is a proper submodule of the simple $L_iw$, hence $\{0\}$, so $U+L_iw=U\oplus L_iw$ has strictly larger dimension — contradicting maximality. Therefore
$$
W=U=\bigoplus_{k=1}^{m}L_{i_k}w_k\cong V^m,
$$
each summand $\cong V$ by (c). $\qquad\blacksquare$ (Necessarily $m=\dim_F W/n$.)

### Remark — Artin–Wedderburn for $M_n(F)$

These four parts are the structure theory of the matrix ring in microcosm. Part (a) says $V$ is **simple**; (b) decomposes the regular module ${}_RR=\bigoplus_{i=1}^n L_i\cong V^n$, so $R$ itself is a sum of copies of its unique simple module — the hallmark of a **semisimple ring**; (c) is **Schur's lemma** in action (a nonzero homomorphic image of a simple module is simple, and indeed isomorphic to it here); and (d) is the **semisimplicity** conclusion: every finite-dimensional module is a direct sum of copies of $V$. (The same maximal-direct-summand argument shows *every* module, not just finite-dimensional ones, is semisimple.) Up to isomorphism $V$ is the *only* simple $R$-module — any simple $W$ has $Lx\ne 0$ for some $x$, forcing $W=Lx\cong V$. This is precisely the Artin–Wedderburn picture: $M_n(F)$ is a simple Artinian ring, $\mathrm{End}_R(V)\cong F$ (Schur), and $R\cong M_n(\mathrm{End}_R(V))=M_n(F)$ — the decomposition of a semisimple ring into matrix algebras, here with a single block.

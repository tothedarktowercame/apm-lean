<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM b93J03: Common eigenvector and simultaneous triangularization for a commuting family

## Why It's Hard

A *single* operator on a finite-dimensional space over an algebraically closed field always has an eigenvector and is triangularizable — that is routine (the characteristic polynomial has a root; Schur/Jordan form). The real content here is doing this **simultaneously for an entire, possibly infinite, family** $A$ of operators at once. The obstruction is that different operators generally have *different* eigenvectors and *different* triangularizing bases, so there is no reason a priori for them to share one — *unless something forces alignment.* That something is **commutativity**, and the whole problem is about extracting geometric mileage from the algebraic relation $ab=ba$.

The key difficulty in part (a) is finding a way to *reduce the dimension*: you need a proper nonzero subspace invariant under the whole family. The non-obvious move is that the eigenspace of *one* non-scalar member is automatically invariant under *all* the others (because they commute with it) — and one must handle the degenerate case where every member is a scalar. Part (b) then has to bootstrap (a) into a full flag, which requires recognizing that "a basis triangularizing every $a$" is the same data as "an $A$-invariant complete flag," and building that flag one common eigenvector at a time via a quotient.

## The Key Insight

**Commuting operators preserve each other's eigenspaces.** If $ab=ba$ and $W=\ker(b-\lambda I)$, then for $w\in W$,
$$
(b-\lambda I)(aw)=a\,(b-\lambda I)w=0\ \Longrightarrow\ aw\in W,
$$
so $W$ is $a$-invariant. Hence the eigenspace of any *non-scalar* member $b\in A$ is a **proper nonzero subspace invariant under the entire family**, which powers a dimension-reduction induction:

- **(a)** Descend into such an eigenspace repeatedly (algebraic closure guarantees an eigenvalue at each step); the dimension drops until the family acts by scalars, where any nonzero vector is a common eigenvector.
- **(b)** A triangularizing basis $v_1,\dots,v_n$ is exactly an $A$-invariant complete flag $0\subset\langle v_1\rangle\subset\langle v_1,v_2\rangle\subset\cdots\subset V$. Build it bottom-up: part (a) supplies a common eigenvector $v_1$ (the bottom of the flag), then pass to the quotient $V/\langle v_1\rangle$ and induct.

## Complete Proof

Let $V$ be finite-dimensional over an algebraically closed field $k$, and let $A$ be a family of pairwise-commuting linear operators on $V$.

### Part (a): a common eigenvector exists

We induct on $n=\dim V$.

**Base case $n=1$.** Every operator on a $1$-dimensional space is multiplication by a scalar, so any nonzero $v\in V$ is an eigenvector of every $a\in A$.

**Inductive step ($n\ge 2$).** Two cases.

*Every $a\in A$ is scalar* (i.e. $a=\mu_a I$ for some $\mu_a\in k$). Then any nonzero $v\in V$ satisfies $av=\mu_a v$ for all $a$, a common eigenvector. Done.

*Some $a_0\in A$ is not scalar.* Since $k$ is algebraically closed, the characteristic polynomial of $a_0$ has a root $\lambda\in k$, so the eigenspace
$$
W:=\ker(a_0-\lambda I)
$$
is nonzero. Moreover $W\ne V$: if $W=V$ then $a_0=\lambda I$ would be scalar, contrary to choice. Thus $0\ne W\subsetneq V$, so $\dim W<n$.

Now $W$ is invariant under the whole family: for any $a\in A$ and $w\in W$, commutativity gives $(a_0-\lambda I)(aw)=a\,(a_0-\lambda I)w=0$, so $aw\in W$. Hence $\{a|_W:a\in A\}$ is a commuting family of operators on $W$, and $\dim W<n$. By the induction hypothesis there is a common eigenvector $v\in W$ for all the $a|_W$ — i.e. $av=\lambda_a v$ for every $a\in A$. Since $W\subseteq V$, this $v$ is a common eigenvector in $V$. $\qquad\blacksquare$ (for (a))

### Part (b): a simultaneous triangularizing basis exists

We show there is an ordered basis $v_1,\dots,v_n$ of $V$ in which every $a\in A$ is upper triangular; equivalently, the subspaces $V_j:=\operatorname{span}(v_1,\dots,v_j)$ form an $A$-invariant flag, $aV_j\subseteq V_j$ for all $a,j$. Induct on $n=\dim V$.

**Base case $n=1$.** Any basis works (every operator is $1\times1$, trivially triangular).

**Inductive step ($n\ge 2$).** By part (a), there is a common eigenvector $v_1$, with $a v_1=\lambda_a v_1$ for each $a\in A$. The line $U=\langle v_1\rangle$ is therefore $A$-invariant, so each $a$ induces a well-defined operator $\bar a$ on the quotient
$$
\bar V:=V/U,\qquad \bar a(\,\overline{x}\,):=\overline{a x},
$$
and the induced family $\{\bar a:a\in A\}$ is commuting on $\bar V$ (since $\overline{ab}=\bar a\,\bar b$ and $ab=ba$), with $\dim\bar V=n-1$. By the induction hypothesis there is a basis $\bar v_2,\dots,\bar v_n$ of $\bar V$ in which every $\bar a$ is upper triangular, i.e.
$$
\bar a\,\bar v_j\in\operatorname{span}(\bar v_2,\dots,\bar v_j)\qquad(2\le j\le n).
$$
Choose any lifts $v_2,\dots,v_n\in V$ (preimages under $V\to\bar V$). Then $v_1,v_2,\dots,v_n$ is a basis of $V$: the images $\bar v_2,\dots,\bar v_n$ are a basis of $V/U$ and $v_1$ spans $U$, so together they are independent and number $n$.

In this basis every $a\in A$ is upper triangular. Indeed $a v_1=\lambda_a v_1\in V_1$. For $j\ge 2$, the relation $\bar a\bar v_j\in\operatorname{span}(\bar v_2,\dots,\bar v_j)$ means
$$
a v_j=\sum_{i=2}^{j}c_{ij}\,v_i+(\text{a multiple of }v_1)\ \in\ \operatorname{span}(v_1,v_2,\dots,v_j)=V_j .
$$
Thus $aV_j\subseteq V_j$ for all $j$, so the matrix of $a$ in $(v_1,\dots,v_n)$ is upper triangular — simultaneously for every $a\in A$. $\qquad\blacksquare$

### Remark — the flag picture and the role of each hypothesis

The two parts are the bottom and the whole of an **$A$-invariant complete flag**. Part (a) produces a $1$-dimensional invariant subspace (a common eigenvector); part (b) iterates this through quotients to produce the full chain $0\subset V_1\subset\cdots\subset V_n=V$ of invariant subspaces, which is precisely the coordinate-free meaning of "simultaneously upper-triangular." Both hypotheses are load-bearing: **algebraic closure** supplies an eigenvalue (hence a $1$-dimensional invariant subspace) at every stage — over $\mathbb{R}$ a rotation has no eigenvector, and even a single operator can fail to be triangularizable; **commutativity** is what makes one operator's eigenspaces invariant under the others, so the whole family can be reduced together. (Diagonalizability is *not* claimed and generally false — a single nilpotent Jordan block already triangularizes but does not diagonalize; the commuting family $A$ here is only simultaneously *triangularizable*. If in addition every member is diagonalizable, the same eigenspace-preservation argument upgrades to simultaneous *diagonalization*, cf. b01J04(a).)

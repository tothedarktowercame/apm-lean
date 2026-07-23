<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m01J01: The Closed Graph Theorem from the Open Mapping Theorem

## Why It's Hard

The Open Mapping Theorem (OMT) and Closed Graph Theorem (CGT) are two of the "big three" pillars of functional analysis (with the Uniform Boundedness Principle), all flowing from Baire category and the completeness of Banach spaces. Parts (a)–(b) test whether one states them *with the right hypotheses* — completeness of **both** spaces is essential (the theorems fail for incomplete spaces), and one must not conflate "closed graph" with the much weaker "closed range" or with continuity itself (continuity always gives a closed graph; the theorem is the nontrivial converse, valid for *linear* maps between *Banach* spaces).

Part (c) is the elegant deduction, and its difficulty is conceptual rather than technical: one must **change the arena**. The map $T$ is hard to control directly, but its graph $\Gamma(T)\subseteq X\times Y$ becomes the central object — a *closed* (by hypothesis) subspace of the Banach space $X\times Y$, hence itself Banach. The "closed graph" hypothesis is precisely what makes $\Gamma$ complete, which is exactly what OMT requires. Seeing that the two coordinate projections convert this into "$\pi_1$ is a continuous bijection with continuous inverse" is the key move.

## The Key Insight

Form the graph $\Gamma(T)=\{(x,Tx):x\in X\}\subseteq X\times Y$. Linearity of $T$ makes it a subspace, and the hypothesis makes it **closed**, hence a Banach space. The two restricted projections
$$
\pi_1:\Gamma\to X,\ (x,Tx)\mapsto x,\qquad \pi_2:\Gamma\to Y,\ (x,Tx)\mapsto Tx
$$
are automatically bounded, and $\pi_1$ is a **continuous bijection of Banach spaces**. By the OMT (bounded inverse corollary), $\pi_1^{-1}:X\to\Gamma$, $x\mapsto(x,Tx)$, is bounded. Then
$$
T=\pi_2\circ\pi_1^{-1}
$$
is a composition of bounded maps, hence bounded. The completeness supplied by the *closed* graph is the entire content.

## Complete Proof

### Part (a): the Open Mapping Theorem

**Theorem (OMT).** Let $X$ and $Y$ be Banach spaces and let $T:X\to Y$ be a bounded (continuous) linear operator that is **surjective**. Then $T$ is an *open map*: the image $T(U)$ of every open set $U\subseteq X$ is open in $Y$. Equivalently, there is a constant $c>0$ such that
$$
T\big(B_X(0,1)\big)\supseteq B_Y(0,c),
$$
i.e. every $y\in Y$ has a preimage $x$ with $\|x\|\le c^{-1}\|y\|$.

**Corollary (Bounded Inverse Theorem).** If, in addition, $T$ is *bijective*, then $T^{-1}:Y\to X$ is bounded. (Indeed $T$ open and bijective means $(T^{-1})^{-1}(U)=T(U)$ is open for every open $U$, so $T^{-1}$ is continuous.)

*(Both spaces must be complete; the theorem rests on the Baire Category Theorem.)*

### Part (b): the Closed Graph Theorem

**Theorem (CGT).** Let $X$ and $Y$ be Banach spaces and let $T:X\to Y$ be a **linear** map. Equip $X\times Y$ with a product norm, e.g. $\|(x,y)\|=\|x\|_X+\|y\|_Y$. If the graph
$$
\Gamma(T)=\{(x,Tx):x\in X\}
$$
is **closed** in $X\times Y$, then $T$ is bounded (continuous).

Equivalently, $T$ is continuous provided: whenever $x_n\to x$ in $X$ *and* $Tx_n\to y$ in $Y$, one has $y=Tx$. (The force of the theorem is that one may assume *both* that $x_n$ converges and that $Tx_n$ converges, rather than having to prove $Tx_n$ converges.)

### Part (c): CGT from OMT

Assume $T:X\to Y$ is linear with closed graph $\Gamma:=\Gamma(T)$.

**$\Gamma$ is a Banach space.** $X\times Y$ with the norm $\|(x,y)\|=\|x\|_X+\|y\|_Y$ is complete (a finite product of Banach spaces is Banach). Since $T$ is linear, $\Gamma$ is a linear subspace; since $\Gamma$ is closed by hypothesis, it is a closed subspace of a Banach space, hence itself complete — a Banach space.

**The coordinate projections.** Define
$$
\pi_1:\Gamma\to X,\quad \pi_1(x,Tx)=x,\qquad \pi_2:\Gamma\to Y,\quad \pi_2(x,Tx)=Tx.
$$
Both are linear, and bounded:
$$
\|\pi_1(x,Tx)\|=\|x\|\le\|x\|+\|Tx\|=\|(x,Tx)\|,\qquad \|\pi_2(x,Tx)\|=\|Tx\|\le\|(x,Tx)\|,
$$
so $\|\pi_1\|,\|\pi_2\|\le 1$.

**$\pi_1$ is a bijection.** It is surjective: every $x\in X$ gives the point $(x,Tx)\in\Gamma$ with $\pi_1(x,Tx)=x$. It is injective: a point of $\Gamma$ is determined by its first coordinate (the second is $Tx$), so $\pi_1(x,Tx)=\pi_1(x',Tx')$ forces $x=x'$, hence the points coincide.

**Apply OMT.** Thus $\pi_1:\Gamma\to X$ is a bounded linear bijection between the Banach spaces $\Gamma$ and $X$. By the Open Mapping Theorem (bounded inverse corollary of part a), its inverse
$$
\pi_1^{-1}:X\to\Gamma,\qquad \pi_1^{-1}(x)=(x,Tx),
$$
is bounded.

**Conclude.** For every $x\in X$,
$$
(\pi_2\circ\pi_1^{-1})(x)=\pi_2(x,Tx)=Tx,
$$
so $T=\pi_2\circ\pi_1^{-1}$. As a composition of the bounded operators $\pi_1^{-1}$ and $\pi_2$, $T$ is bounded. $\qquad\blacksquare$

### Remark — why the hypotheses are exactly right

The proof isolates what "closed graph" buys: it makes $\Gamma$ a *complete* space, which is the only thing needed to feed $\pi_1$ into the OMT. Completeness of **both** $X$ and $Y$ is used — $Y$'s completeness goes into making $X\times Y$ (hence $\Gamma$) Banach, and $X$'s completeness is needed for OMT to apply to $\pi_1:\Gamma\to X$. The CGT and OMT (and the Bounded Inverse Theorem) are in fact *equivalent* — each can be derived from the others — and all are equivalent to a Baire-category statement; this problem establishes one direction of that web. The practical value of CGT is that it converts the hard task of proving $T$ continuous ("$x_n\to x\Rightarrow Tx_n\to Tx$") into the often-easier task of checking the graph is closed ("$x_n\to x$ and $Tx_n\to y\Rightarrow y=Tx$"), where one is *handed* the convergence of $Tx_n$ for free — a constant labor-saver in proving operators (e.g. differential operators, multiplication operators) are bounded.

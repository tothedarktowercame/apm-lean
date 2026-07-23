<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m00A03: Riesz's lemma and the spectrum of a compact operator accumulates only at 0

## Why It's Hard

In a general Banach space there is **no inner product**, hence no orthogonal projection and no way to manufacture orthonormal sequences — the standard Hilbert-space tool. Part (a) is the celebrated substitute, **Riesz's lemma**: given a proper closed subspace, one can find a unit vector that is "almost orthogonal" to it (distance $\ge\tfrac12$). The difficulty is the construction — there is no nearest point in general, so one must take a vector *within a factor of $2$* of the infimum distance and normalize, and verify that subtracting an arbitrary element of the subspace from the normalized vector pulls back to subtracting an element from the original. The constant $\tfrac12$ is exactly the price of that factor-$2$ slack (distance $1$ is unattainable in infinite dimensions).

Part (b) is a cornerstone of spectral theory whose proof is genuinely subtle: to show $\sigma(A)\cap\{|z|\ge\epsilon\}$ is finite, one assumes infinitely many eigenvalues $|\lambda_n|\ge\epsilon$, builds the **strictly increasing flag** of eigenspaces, and then — this is where (a) is indispensable — extracts Riesz-lemma unit vectors $z_n$ that force the images $Az_n$ to stay a fixed distance $\ge\epsilon/2$ apart, contradicting compactness. Marrying "almost-orthogonal vectors" to "the invariant flag of a compact operator" is the crux, and it is the reason part (a) precedes part (b).

## The Key Insight

**(a)** Pick $w\in Z\setminus Y$; since $Y$ is closed, $d=\operatorname{dist}(w,Y)>0$. Choose $y_0\in Y$ with $d\le\|w-y_0\|\le 2d$ and set $z=\frac{w-y_0}{\|w-y_0\|}$. For any $y\in Y$, $y_0+\|w-y_0\|y\in Y$, so $\|z-y\|=\frac{\|w-(y_0+\|w-y_0\|y)\|}{\|w-y_0\|}\ge\frac{d}{\|w-y_0\|}\ge\frac{d}{2d}=\frac12$.

**(b)** The nonzero spectrum of a compact operator consists of eigenvalues. If infinitely many distinct eigenvalues had $|\lambda_n|\ge\epsilon$, their eigenvectors give a strictly increasing chain $Z_1\subsetneq Z_2\subsetneq\cdots$ of finite-dimensional ($A$-invariant) subspaces with the key shift property $(A-\lambda_n I)Z_n\subseteq Z_{n-1}$. Applying (a) to each $Z_{n-1}\subsetneq Z_n$ gives unit $z_n$ with $\operatorname{dist}(z_n,Z_{n-1})\ge\tfrac12$, and then for $m>n$,
$$
\|Az_m-Az_n\|=|\lambda_m|\,\Big\|z_m-\tfrac{u}{\lambda_m}\Big\|\ge|\lambda_m|\cdot\tfrac12\ge\tfrac{\epsilon}{2},\qquad u\in Z_{m-1},
$$
so $(Az_n)$ has no convergent subsequence — impossible for compact $A$ on the bounded $(z_n)$. Hence each annulus $\{|z|\ge\epsilon\}$ meets $\sigma(A)$ finitely, forcing all accumulation at $0$.

## Complete Proof

### Part (a): Riesz's lemma

Let $Y\subsetneq Z$ with $Y$ a proper closed subspace of the subspace $Z\subseteq X$. Choose $w\in Z\setminus Y$. Since $Y$ is closed,
$$
d:=\operatorname{dist}(w,Y)=\inf_{y\in Y}\|w-y\|>0
$$
(if $d=0$ then $w\in\overline Y=Y$, a contradiction). By definition of the infimum, $d<2d$, so there exists $y_0\in Y$ with
$$
d\le\|w-y_0\|\le 2d .
$$
Put $z=\dfrac{w-y_0}{\|w-y_0\|}\in Z$ (as $w,y_0\in Z$), so $\|z\|=1$. For any $y\in Y$, the element $y':=y_0+\|w-y_0\|\,y$ lies in $Y$ (subspace), and
$$
\|z-y\|=\frac{1}{\|w-y_0\|}\big\|\,(w-y_0)-\|w-y_0\|\,y\,\big\|=\frac{\|w-y'\|}{\|w-y_0\|}\ge\frac{d}{\|w-y_0\|}\ge\frac{d}{2d}=\frac12 .
$$
Hence $\operatorname{dist}(z,Y)\ge\tfrac12$ with $\|z\|=1$. $\qquad\checkmark$

### Part (b): $0$ is the only possible limit point of $\sigma(A)$

It suffices to show that for every $\epsilon>0$, the set $\sigma(A)\cap\{z:|z|\ge\epsilon\}$ is **finite**; then any limit point $\mu$ of $\sigma(A)$ with $\mu\ne 0$ would (taking $\epsilon=|\mu|/2$) force infinitely many spectral points in $\{|z|\ge\epsilon\}$, a contradiction — so every limit point is $0$.

We use the **Riesz–Schauder theorem**: for a compact operator $A$ on a Banach space and $\lambda\ne 0$, every $\lambda\in\sigma(A)$ is an eigenvalue (since $\lambda I-A$ is Fredholm of index $0$, so failure of invertibility means failure of injectivity).

Suppose, for contradiction, that for some $\epsilon>0$ there are infinitely many points of $\sigma(A)$ with modulus $\ge\epsilon$. Pick distinct eigenvalues $\lambda_1,\lambda_2,\dots$ with $|\lambda_n|\ge\epsilon$ and eigenvectors $Ax_n=\lambda_n x_n$, $x_n\ne 0$.

**The flag.** Eigenvectors for distinct eigenvalues are linearly independent, so $Z_n:=\operatorname{span}\{x_1,\dots,x_n\}$ satisfies $Z_{n-1}\subsetneq Z_n$, each finite-dimensional (hence closed). Each $Z_n$ is $A$-invariant ($Ax_k=\lambda_kx_k\in Z_n$ for $k\le n$), and the crucial shift property holds: for $v=\sum_{k=1}^n c_kx_k\in Z_n$,
$$
(A-\lambda_n I)v=\sum_{k=1}^{n}c_k(\lambda_k-\lambda_n)x_k=\sum_{k=1}^{n-1}c_k(\lambda_k-\lambda_n)x_k\in Z_{n-1},
$$
since the $k=n$ term vanishes. So $(A-\lambda_n I)Z_n\subseteq Z_{n-1}$.

**Almost-orthogonal vectors.** By part (a) applied to $Z_{n-1}\subsetneq Z_n$, choose $z_n\in Z_n$ with $\|z_n\|=1$ and $\operatorname{dist}(z_n,Z_{n-1})\ge\tfrac12$.

**No convergent subsequence of $(Az_n)$.** Fix $m>n$. Write
$$
Az_m=\lambda_m z_m-(\lambda_m I-A)z_m,
$$
so
$$
Az_m-Az_n=\lambda_m z_m-\underbrace{\big[(\lambda_m I-A)z_m+Az_n\big]}_{=:u}.
$$
Here $(\lambda_m I-A)z_m\in Z_{m-1}$ by the shift property, and $Az_n\in Z_n\subseteq Z_{m-1}$ (as $n\le m-1$ and $Z_n$ is $A$-invariant); hence $u\in Z_{m-1}$. Therefore
$$
\|Az_m-Az_n\|=|\lambda_m|\,\Big\|z_m-\tfrac{u}{\lambda_m}\Big\|\ge|\lambda_m|\cdot\operatorname{dist}(z_m,Z_{m-1})\ge|\lambda_m|\cdot\tfrac12\ge\frac{\epsilon}{2},
$$
using $u/\lambda_m\in Z_{m-1}$. Thus $\|Az_m-Az_n\|\ge\epsilon/2$ for all $m\ne n$, so $(Az_n)$ has no Cauchy (hence no convergent) subsequence.

But $(z_n)$ is bounded ($\|z_n\|=1$) and $A$ is compact, so $(Az_n)$ *must* have a convergent subsequence — a contradiction. Therefore only finitely many spectral points have modulus $\ge\epsilon$, for every $\epsilon>0$, and $0$ is the only possible limit point of $\sigma(A)$. $\qquad\blacksquare$

### Remark — the architecture of Riesz theory

Part (a) is the engine and part (b) the payoff, and the dependence is essential: Riesz's lemma is precisely the Banach-space replacement for orthonormal sequences, supplying unit vectors "spread out" relative to a growing chain of subspaces. The same lemma proves that the closed unit ball of an infinite-dimensional normed space is *never* compact (take $Y=Z_{n-1}$ a hyperplane chain to build a $\tfrac12$-separated sequence with no convergent subsequence) — and part (b) is morally that statement applied to the eigenspaces of $A$. The conclusion is half of the **spectral theorem for compact operators**: $\sigma(A)$ is a countable set whose only possible accumulation point is $0$, with every nonzero $\lambda$ an eigenvalue of finite multiplicity. In Hilbert space with $A$ self-adjoint this upgrades to the full eigenfunction expansion, but the accumulation-only-at-$0$ part needs nothing beyond compactness and Riesz's lemma. (Note $0$ itself need not be an eigenvalue, and in infinite dimensions $0\in\sigma(A)$ always, since a compact operator cannot be invertible.)

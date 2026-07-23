<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m01J03: (T*T)^n converges to the orthogonal projection onto the top eigenspace

## Why It's Hard

The statement looks like it could need functional calculus or heavy machinery,
but the entire problem is the **spectral theorem for compact self-adjoint
operators** read through the lens of "what does raising eigenvalues to the $n$th
power do?" The first job is recognizing the right object: not $T$ itself (which
need not be self-adjoint or have eigenvalues) but $S=T^{*}T$, which is compact,
**self-adjoint**, **positive**, and has $\|S\|=\|T\|^{2}=1$. The crux is then a
spectral-gap fact that is easy to under-prove: because the nonzero eigenvalues of
a compact operator can only accumulate at $0$, the eigenvalue $1$ is **isolated**
— there is a gap $(1-\varepsilon,1)$ free of spectrum — so the eigenvalues split
cleanly into "$=1$" and "$\le 1-\varepsilon$." Powers then quench every eigenvalue
below $1$ geometrically while fixing the top eigenspace, and the limit is its
projection. The finite-dimensionality of $A$ is exactly the Riesz fact that a
nonzero eigenvalue of a compact operator has a finite-dimensional eigenspace. The
trap is forgetting to justify (i) that $1$ is actually attained as an eigenvalue
and (ii) the gap — without the gap you only get strong, not norm, convergence,
and you cannot bound the tail uniformly.

## The Key Insight

Set $S=T^{*}T$. Then $S=S^{*}$, $S\ge0$ ($\langle Sx,x\rangle=\|Tx\|^{2}$), $S$ is
compact, and $\|S\|=\|T\|^{2}=1$. The spectral theorem gives an orthonormal system
of eigenvectors $\{e_k\}$ with eigenvalues $\lambda_k\in(0,1]$, $\lambda_k\to0$,
and
$$
Sx=\sum_k\lambda_k\langle x,e_k\rangle e_k,\qquad
S^{n}x=\sum_k\lambda_k^{\,n}\langle x,e_k\rangle e_k .
$$
Since $\|S\|=1$ is attained, $\lambda=1$ **is** an eigenvalue; let
$A=\ker(S-I)$, finite-dimensional (compactness). Because nonzero eigenvalues
accumulate only at $0$, there is $\varepsilon>0$ with every eigenvalue either
$=1$ or $\le 1-\varepsilon=:\mu<1$. Splitting off the eigenvalue-$1$ part (which
is $P_A$) leaves a tail damped by $\mu^{n}$:
$$
\|S^{n}x-P_Ax\|^{2}=\sum_{\lambda_k<1}\lambda_k^{2n}|\langle x,e_k\rangle|^{2}
\le\mu^{2n}\|x\|^{2}\ \Longrightarrow\ \|S^{n}-P_A\|\le\mu^{n}\to0 .
$$

## Complete Proof

### Step 1: $S=T^{*}T$ is compact, self-adjoint, positive, with $\|S\|=1$

$S^{*}=(T^{*}T)^{*}=T^{*}T=S$, so $S$ is self-adjoint. For all $x$,
$$
\langle Sx,x\rangle=\langle T^{*}Tx,x\rangle=\langle Tx,Tx\rangle=\|Tx\|^{2}\ge0,
$$
so $S\ge0$ (in particular all eigenvalues are $\ge0$). $T$ compact implies
$T^{*}$ compact, and the product of a compact operator with a bounded operator is
compact, so $S=T^{*}T$ is **compact**. Finally, the $C^{*}$-identity gives
$$
\|S\|=\|T^{*}T\|=\|T\|^{2}=1 .
$$
Note also $\ker S=\ker T$: if $Tx=0$ then $Sx=T^{*}Tx=0$; conversely $Sx=0$ gives
$\|Tx\|^{2}=\langle Sx,x\rangle=0$.

### Step 2: spectral decomposition of $S$

By the **spectral theorem for compact self-adjoint operators**, there is a finite
or countable orthonormal system $\{e_k\}$ of eigenvectors of $S$ with nonzero
eigenvalues $\lambda_k$ — each nonzero eigenvalue of finite multiplicity, repeated
accordingly, and $\lambda_k\to0$ if there are infinitely many — such that
$$
Sx=\sum_k\lambda_k\,\langle x,e_k\rangle\,e_k\qquad(x\in H),
$$
with $\{e_k\}$ together with an orthonormal basis of $\ker S$ forming an
orthonormal basis of $H$. By Step 1 each $\lambda_k>0$, and since $S\ge0$ with
$\|S\|=1$,
$$
\|S\|=\max_k\lambda_k=1 .
$$
This maximum is **attained**: the $\lambda_k$ accumulate only at $0$, so the
largest one is achieved by some eigenvector. Hence $1$ is an eigenvalue of $S$,
and
$$
A:=\ker(S-I)=\{x:Sx=x\}\neq\{0\}.
$$
Because $1\neq0$ and $S$ is compact, $A$ is **finite-dimensional** (the eigenspace
of a compact operator for a nonzero eigenvalue is finite-dimensional). Choose the
labelling so that the eigenvectors $e_k$ with $\lambda_k=1$ form an orthonormal
basis of $A$; then the orthogonal projection onto $A$ is
$$
P_A x=\sum_{\lambda_k=1}\langle x,e_k\rangle\,e_k .
$$

### Step 3: the spectral gap at $1$

The nonzero eigenvalues of the compact operator $S$ have $0$ as their only
possible accumulation point. Consequently **no sequence of eigenvalues can
approach $1$ from below**: if eigenvalues $\lambda<1$ accumulated at $1$, that
would be a nonzero accumulation point, a contradiction. Therefore there exists
$\varepsilon\in(0,1)$ such that the interval $(1-\varepsilon,1)$ contains no
eigenvalue of $S$. Setting
$$
\mu:=\sup\{\lambda_k:\lambda_k<1\}\le 1-\varepsilon<1
$$
(with the convention $\mu=0$ if $1$ is the only nonzero eigenvalue), every
eigenvalue is either $=1$ or $\le\mu<1$.

### Step 4: powers and the limit

For each $x\in H$, applying $S$ repeatedly to its expansion,
$$
S^{n}x=\sum_k\lambda_k^{\,n}\langle x,e_k\rangle e_k
=\underbrace{\sum_{\lambda_k=1}\langle x,e_k\rangle e_k}_{=\,P_Ax}
\;+\;\sum_{\lambda_k<1}\lambda_k^{\,n}\langle x,e_k\rangle e_k ,
$$
where the $\ker S$ component contributes $0$ (eigenvalue $0$, and $n\ge1$). By
orthonormality of $\{e_k\}$ and Step 3,
$$
\|S^{n}x-P_Ax\|^{2}
=\sum_{\lambda_k<1}\lambda_k^{\,2n}\,|\langle x,e_k\rangle|^{2}
\le\mu^{2n}\sum_{k}|\langle x,e_k\rangle|^{2}
\le\mu^{2n}\,\|x\|^{2},
$$
using Bessel's inequality $\sum_k|\langle x,e_k\rangle|^{2}\le\|x\|^{2}$. Taking the
supremum over $\|x\|\le1$ gives the **operator-norm** bound
$$
\|S^{n}-P_A\|\le\mu^{n}\xrightarrow[n\to\infty]{}0,
$$
since $\mu<1$. Therefore
$$
(T^{*}T)^{n}=S^{n}\ \longrightarrow\ P_A\quad\text{in operator norm,}
$$
where $P_A$ is the orthogonal projection onto the finite-dimensional subspace
$A=\ker(T^{*}T-I)\neq\{0\}$. $\quad\blacksquare$

### Remark

The whole phenomenon is "raising eigenvalues to high powers acts as a hard
threshold": values $<1$ are crushed geometrically, the value $1$ survives, and
$0$-modes are gone after one step — so $S^{n}\to P_{\{\lambda=1\}}$. Two compact
self-adjoint facts make it rigorous and sharp: the eigenspace $A=\ker(S-I)$ is
**finite-dimensional** (giving the projection a finite-dimensional range), and the
eigenvalues' **only accumulation point is $0$** (giving the gap $\mu<1$, hence
*norm* convergence at the explicit geometric rate $\mu^{n}$, not merely strong
convergence). Concretely $A=\{x:\|Tx\|=\|x\|\}$, the subspace on which $T$ is
norm-preserving — the directions where the operator of norm $1$ "achieves its
norm." Equivalently, in the singular value decomposition of $T$, $A$ is the span
of the right singular vectors with singular value $1$.

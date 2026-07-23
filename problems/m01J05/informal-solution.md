<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m01J05: The contraction mapping theorem, and local convergence of Newton's method

## Why It's Hard

The contraction mapping theorem itself is a clean Cauchy-sequence argument, but its
*application* to Newton's method is where the insight lies. Newton's iteration is just
fixed-point iteration for $G(x)=x-DF(x)^{-1}F(x)$, and the reason it works (and works
*fast*) is the remarkable identity $DG(x_*)=0$: the linearization of the Newton map
vanishes at the root. Establishing this requires the product rule on the matrix-valued map
$x\mapsto DF(x)^{-1}F(x)$ and the observation that the troublesome term dies because
$F(x_*)=0$. Once $DG(x_*)=0$, continuity of $DG$ makes $G$ a contraction with as small a
constant as desired on a small ball — and the abstract theorem closes the argument.

## The Key Insight

- **(a)** Iterates satisfy $d(x_{n+1},x_n)\le q^n d(x_1,x_0)$, so $d(x_m,x_n)\le
  \frac{q^n}{1-q}d(x_1,x_0)\to0$: Cauchy, hence convergent to the (unique) fixed point.
- **(b)** $G(x_*)=x_*$, and $DG(x)=I-\big(D[DF(x)^{-1}]\,F(x)+DF(x)^{-1}DF(x)\big)$; at
  $x_*$ the first term vanishes ($F(x_*)=0$) and the second is $I$, so $DG(x_*)=0$.
  Continuity of $DG$ gives $\|DG\|\le\tfrac12$ on a ball $\overline B(x_*,\epsilon)$, on
  which $G$ is a $\tfrac12$-contraction mapping the ball into itself; apply (a).

## Complete Proof

### (a) The Contraction Mapping Theorem

**Statement.** Let $(X,d)$ be a complete metric space and $T:X\to X$ a *contraction*:
there is $q\in[0,1)$ with $d(Tx,Ty)\le q\,d(x,y)$ for all $x,y\in X$. Then $T$ has a unique
fixed point $x_*\in X$, and for every $x_0\in X$ the iterates $x_{n+1}=Tx_n$ converge to
$x_*$.

**Proof.** Fix $x_0$ and set $x_{n+1}=Tx_n$. By induction,
$$
d(x_{n+1},x_n)=d(Tx_n,Tx_{n-1})\le q\,d(x_n,x_{n-1})\le\cdots\le q^n\,d(x_1,x_0).
$$
Hence for $m>n$, by the triangle inequality and the geometric series,
$$
d(x_m,x_n)\le\sum_{k=n}^{m-1}d(x_{k+1},x_k)\le\Big(\sum_{k=n}^{m-1}q^k\Big)d(x_1,x_0)
\le\frac{q^n}{1-q}\,d(x_1,x_0)\xrightarrow[n\to\infty]{}0 .
$$
So $(x_n)$ is Cauchy; by completeness $x_n\to x_*$ for some $x_*\in X$. A contraction is
(Lipschitz, hence) continuous, so
$$
x_*=\lim_n x_{n+1}=\lim_n T x_n=T\big(\lim_n x_n\big)=Tx_* ,
$$
i.e. $x_*$ is a fixed point. **Uniqueness:** if $Tx_*=x_*$ and $Ty_*=y_*$, then
$d(x_*,y_*)=d(Tx_*,Ty_*)\le q\,d(x_*,y_*)$, so $(1-q)d(x_*,y_*)\le0$; since $q<1$,
$d(x_*,y_*)=0$, i.e. $x_*=y_*$. The convergence statement for arbitrary $x_0$ is exactly
what we proved. $\quad\blacksquare$

### (b) Local convergence of Newton's method

$F:\mathbb R^n\to\mathbb R^n$ is smooth, $x_*$ a simple root: $F(x_*)=0$ and $DF(x_*)$
invertible. Let $G(x)=x-DF(x)^{-1}F(x)$, $x_{k+1}=G(x_k)$.

**$x_*$ is a fixed point of $G$.** $G(x_*)=x_*-DF(x_*)^{-1}F(x_*)=x_*-DF(x_*)^{-1}\cdot0=
x_*$.

**$G$ is defined and smooth near $x_*$.** The set of invertible matrices is open and
$x\mapsto DF(x)$ is continuous, so $DF(x)$ is invertible for $x$ in some ball
$B(x_*,r)$; on that ball matrix inversion is smooth, so $G$ is smooth.

**$DG(x_*)=0$.** Write $A(x)=DF(x)^{-1}$ (matrix-valued, smooth near $x_*$), so
$G(x)=x-A(x)F(x)$. By the product rule applied to the map $x\mapsto A(x)F(x)$,
$$
DG(x)=I-\Big(\big[DA(x)\big]\,F(x)+A(x)\,DF(x)\Big),
$$
where $[DA(x)]F(x)$ denotes the derivative of $A$ contracted against the vector $F(x)$. At
$x=x_*$, the first inner term vanishes because $F(x_*)=0$, and $A(x_*)DF(x_*)=
DF(x_*)^{-1}DF(x_*)=I$. Therefore
$$
DG(x_*)=I-\big(0+I\big)=0 .
$$

**$G$ is a strict contraction on a small ball.** Since $DG$ is continuous and
$DG(x_*)=0$, there is $\epsilon\in(0,r]$ such that
$$
\|DG(x)\|\le \tfrac12\qquad\text{for all }x\in \overline B(x_*,\epsilon).
$$
The closed ball $\overline B(x_*,\epsilon)$ is convex, so for $x,y$ in it the mean-value
inequality (integrate $DG$ along the segment) gives
$$
|G(x)-G(y)|\le\Big(\sup_{[x,y]}\|DG\|\Big)|x-y|\le\tfrac12|x-y| .
$$
Thus $G$ is a $\tfrac12$-contraction there. Moreover $G$ maps the ball into itself: for
$x\in\overline B(x_*,\epsilon)$,
$$
|G(x)-x_*|=|G(x)-G(x_*)|\le\tfrac12|x-x_*|\le\tfrac{\epsilon}{2}\le\epsilon .
$$

**Conclusion.** $X=\overline B(x_*,\epsilon)$ is a closed subset of $\mathbb R^n$, hence a
complete metric space, and $G:X\to X$ is a contraction. By part (a), $G$ has a unique fixed
point in $X$ — necessarily $x_*$ — and for **any** $x_0$ with $|x_0-x_*|\le\epsilon$, the
iterates stay in $X$ (so each $DF(x_k)$ is invertible and $x_{k+1}=G(x_k)$ is well-defined)
and converge to $x_*$:
$$
|x_k-x_*|\le\big(\tfrac12\big)^k|x_0-x_*|\to0 . \qquad\blacksquare
$$

### Remark

$DG(x_*)=0$ is the algebraic signature of Newton's method and the source of its celebrated
*quadratic* convergence: since the first derivative of the iteration map vanishes at the
root, a second-order Taylor expansion gives $|x_{k+1}-x_*|\le C|x_k-x_*|^2$ near $x_*$
(when $F\in C^2$), far faster than the geometric rate the contraction theorem guarantees.
The contraction theorem supplies the *basin of attraction* (a ball of radius $\epsilon$
within which convergence is certain); the quadratic rate is the bonus from the vanishing
derivative. Simplicity of the root — invertibility of $DF(x_*)$ — is exactly what makes
$G$ well-defined and $DG(x_*)=0$; at a multiple root Newton degrades to linear convergence.

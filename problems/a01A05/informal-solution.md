# APM a01A05: Nearly orthogonal sequences in a Hilbert space

## Result

Part (a) is false as printed. The stated hypotheses do not imply

$$
\lVert f_m-e_m\rVert\le 2^{-m}.
$$

Part (b) is true: the sequence $(f_m)$ converges weakly to zero.

## Part (a): A counterexample

It is enough to work in the real Hilbert space $\ell^2(\mathbb N)$. Let
$(u_n)_{n\geq 0}$ be its standard orthonormal basis and put

$$
f_0=u_0,\qquad
f_1=\frac12u_0+\frac{\sqrt3}{2}u_1,\qquad
f_m=u_m\quad(m\geq2).
$$

Every $f_m$ has norm one. The only nonzero inner product between two distinct
members of the sequence is

$$
\langle f_0,f_1\rangle=\frac12=2^{-1};
$$

all inner products involving $f_m$ for $m\geq2$ vanish. Thus the sequence
satisfies the stated bound
$|\langle f_n,f_m\rangle|\leq2^{-m}$ whenever $n<m$.

At the second Gram--Schmidt step, subtracting the projection onto $f_0$ gives

$$
f_1-\langle f_0,f_1\rangle f_0
  =\frac{\sqrt3}{2}u_1.
$$

After normalization, $e_1=u_1$. Consequently

$$
\begin{aligned}
\lVert f_1-e_1\rVert^2
 &=\left\lVert \frac12u_0+
       \left(\frac{\sqrt3}{2}-1\right)u_1\right\rVert^2\\
 &=\frac14+\left(\frac{\sqrt3}{2}-1\right)^2
  =2-\sqrt3.
\end{aligned}
$$

Since $2-\sqrt3>1/4$, we have
$\lVert f_1-e_1\rVert>1/2=2^{-1}$. This contradicts the proposed estimate.
Thus part (a), as written, cannot be proved.

## Part (b): Weak convergence to zero

Let $H$ be the real Hilbert space containing the sequence, and let

$$
K=\overline{\operatorname{span}\{f_n:n\geq0\}}.
$$

We first prove the desired limit for vectors in the algebraic span. For a
fixed $n$, the hypothesis gives, for every $m>n$,

$$
|\langle f_n,f_m\rangle|\leq2^{-m}\longrightarrow0.
$$

By linearity, it follows that
$\langle v,f_m\rangle\to0$ for every finite linear combination $v$ of the
$f_n$.

Now let $v\in K$. Given $\varepsilon>0$, choose a finite linear combination
$w$ with $\lVert v-w\rVert<\varepsilon/2$. Since every $f_m$ has norm one,
Cauchy--Schwarz gives

$$
|\langle v,f_m\rangle|
 \leq |\langle w,f_m\rangle|
      +|\langle v-w,f_m\rangle|
 \leq |\langle w,f_m\rangle|+\lVert v-w\rVert.
$$

For all sufficiently large $m$, the first term is below $\varepsilon/2$;
hence $\langle v,f_m\rangle\to0$ for every $v\in K$.

Finally take an arbitrary $g\in H$ and let $P_Kg$ be its orthogonal projection
onto $K$. Since each $f_m$ belongs to $K$, the orthogonal component
$g-P_Kg$ has zero inner product with $f_m$. Therefore

$$
\langle g,f_m\rangle=\langle P_Kg,f_m\rangle\longrightarrow0.
$$

In the original $L^2$ notation this says

$$
\int g(x)f_m(x)\,dx\longrightarrow0,
$$

which proves part (b).

## Relation to the Lean proof

The formal theorem records the failure of the universal estimate in part (a)
and the valid weak-convergence assertion in part (b). Its counterexample is the
$\ell^2$ sequence above, using Mathlib's normalized Gram--Schmidt construction.
The weak-convergence proof follows the same span, closure, and orthogonal
projection argument.

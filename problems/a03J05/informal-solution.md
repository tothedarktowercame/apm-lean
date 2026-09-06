# APM a03J05: A cosine integral

We compute, for $t\in\mathbb R$,

$$
I(t)=\int_0^\infty\frac{\cos(tx)}{1+x^2}\,dx.
$$

The answer is

$$
\boxed{I(t)=\frac{\pi}{2}e^{-|t|}}.
$$

## Contour calculation

First suppose $t>0$ and consider

$$
F_t(z)=\frac{e^{itz}}{1+z^2}.
$$

Integrate $F_t$ over the upper semicircle of radius $R>1$. The only pole
inside is the simple pole at $z=i$, whose residue is

$$
\operatorname{Res}_{z=i}F_t(z)
 =\frac{e^{it i}}{2i}
 =\frac{e^{-t}}{2i}.
$$

The residue theorem therefore gives

$$
\int_{-R}^{R}\frac{e^{itx}}{1+x^2}\,dx
 +\int_{\Gamma_R}\frac{e^{itz}}{1+z^2}\,dz
 =\pi e^{-t},
$$

where $\Gamma_R$ is the upper semicircular arc.

On that arc, $|e^{itz}|=e^{-t\operatorname{Im}z}\leq1$, while
$|1+z^2|\geq R^2-1$. Since the arc has length $\pi R$,

$$
\left|\int_{\Gamma_R}\frac{e^{itz}}{1+z^2}\,dz\right|
 \leq\frac{\pi R}{R^2-1}\longrightarrow0.
$$

Letting $R\to\infty$ yields

$$
\int_{-\infty}^{\infty}\frac{e^{itx}}{1+x^2}\,dx=\pi e^{-t}
\qquad(t>0).
$$

For $t<0$, close the contour in the lower half-plane. The contour is clockwise
and encloses the pole at $z=-i$. Its residue is

$$
\operatorname{Res}_{z=-i}F_t(z)
 =\frac{e^{it(-i)}}{-2i}=\frac{e^t}{-2i}.
$$

The clockwise residue theorem and the same arc estimate give

$$
\int_{-\infty}^{\infty}\frac{e^{itx}}{1+x^2}\,dx
 =\pi e^t=\pi e^{-|t|}.
$$

At $t=0$, direct integration gives

$$
\int_{-\infty}^{\infty}\frac{dx}{1+x^2}
 =\left[\arctan x\right]_{-\infty}^{\infty}=\pi,
$$

so the same formula holds for every real $t$.

## Return to the half-line

Taking real parts gives

$$
\int_{-\infty}^{\infty}\frac{\cos(tx)}{1+x^2}\,dx
 =\pi e^{-|t|}.
$$

The integrand is even in $x$, hence the full-line integral is twice the
half-line integral. Therefore

$$
I(t)=\frac12\pi e^{-|t|}
     =\boxed{\frac\pi2e^{-|t|}}.
$$

## Relation to the Lean proof

The formal proof reaches the same full-line identity by Fourier inversion
rather than by formalizing a semicircular contour. It first computes the
Fourier transform of $x\mapsto e^{-|x|}$ from the Laplace cosine integral,
shows that the sine part vanishes by oddness, applies Fourier inversion, and
rescales by $2\pi$. Evenness then converts the full-line identity into the
requested half-line integral. The theorem covers every real $t$, including
$t=0$.

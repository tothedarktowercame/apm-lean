<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J06: A cosine transform of the Poisson kernel via contour integration

## Why It's Hard

The integral $\displaystyle \int_0^{\infty} \frac{\cos(tx)}{x^2+4}\,dx$ has no
elementary antiderivative — you cannot finish it with substitution or integration
by parts. It is an *oscillatory* improper integral whose closed form,
$\frac{\pi}{4}e^{-2|t|}$, is not something the integrand wears on its sleeve: a
rational-times-cosine integrand producing a clean decaying exponential in the
parameter $t$ is exactly the kind of "where did that come from?" answer that the
real-variable toolkit does not readily explain.

Three things have to be handled with care:

1. **Getting a closed form at all.** The honest routes are complex (residues),
   or a parameter trick (an ODE in $t$, or differentiating a known transform).
   Either way you must leave the real line.

2. **The absolute value $|t|$.** The final answer depends on $t$ only through
   $|t|$, and that kink at $t = 0$ is not an accident to be papered over — it is
   forced by the method. When you complexify $\cos(tx) = \Re\, e^{itx}$, the sign
   of $t$ decides which half-plane the integrand decays in, hence which pole you
   enclose. Sign of $t$ in, $|t|$ out.

3. **Justifying the contour.** You must show the large semicircular arc
   contributes nothing in the limit, and that taking the real part commutes with
   the (absolutely convergent) integral.

## The Key Insight

Replace $\cos(tx)$ by $\Re\, e^{itx}$ and double the domain using evenness:
$$\int_0^{\infty} \frac{\cos(tx)}{x^2+4}\,dx
   = \frac{1}{2}\int_{-\infty}^{\infty} \frac{\cos(tx)}{x^2+4}\,dx
   = \frac{1}{2}\,\Re \int_{-\infty}^{\infty} \frac{e^{itx}}{x^2+4}\,dx .$$
Now $\dfrac{e^{itz}}{z^2+4}$ is meromorphic with simple poles at $z = \pm 2i$. For
$t \ge 0$ the factor $|e^{itz}| = e^{-t\,\Im z}$ decays in the **upper** half-plane,
so we close the contour upward and enclose only the pole at $z = 2i$; a single
residue delivers the whole integral. Because the original integral is even in $t$
(as $\cos$ is), the $t \ge 0$ computation extends to all real $t$ by replacing $t$
with $|t|$.

## Complete Proof

**Claim.** For every real $t$,
$$\int_0^{\infty} \frac{\cos(tx)}{x^2+4}\,dx = \frac{\pi}{4}\,e^{-2|t|}.$$

**Convergence and reductions.** The integrand is dominated by
$\frac{1}{x^2+4} \in L^1(\R)$ since $|\cos(tx)| \le 1$, so the integral converges
absolutely for every $t$. The integrand $\frac{\cos(tx)}{x^2+4}$ is even in $x$,
hence
$$I(t) := \int_0^{\infty} \frac{\cos(tx)}{x^2+4}\,dx
       = \frac{1}{2}\int_{-\infty}^{\infty} \frac{\cos(tx)}{x^2+4}\,dx .$$
Also $\cos$ is even in $t$, so $I(t) = I(|t|)$; it therefore suffices to evaluate
$I(t)$ for $t \ge 0$ and then write $|t|$ in the answer.

**Setting up the contour (fix $t \ge 0$).** Since $\sin(tx)/(x^2+4)$ is odd in $x$,
$\int_{-\infty}^{\infty} \frac{\sin(tx)}{x^2+4}\,dx = 0$, and so
$$\int_{-\infty}^{\infty} \frac{\cos(tx)}{x^2+4}\,dx
   = \Re \int_{-\infty}^{\infty} \frac{e^{itx}}{x^2+4}\,dx
   = \int_{-\infty}^{\infty} \frac{e^{itx}}{x^2+4}\,dx ,$$
the last equality because the right-hand integral will turn out real. Consider
$$f(z) = \frac{e^{itz}}{z^2+4} = \frac{e^{itz}}{(z-2i)(z+2i)},$$
and integrate over the closed contour $\Gamma_R$ consisting of the segment
$[-R, R]$ on the real axis followed by the semicircular arc
$C_R = \{R e^{i\theta} : 0 \le \theta \le \pi\}$ in the upper half-plane, traversed
counterclockwise. For $R > 2$ the only singularity of $f$ inside $\Gamma_R$ is the
simple pole at $z = 2i$.

**The arc vanishes.** On $C_R$ we have $\Im z \ge 0$, so $|e^{itz}| = e^{-t\,\Im z}
\le 1$ for $t \ge 0$, while $|z^2 + 4| \ge R^2 - 4$. Hence by the ML-estimate
$$\left| \int_{C_R} f(z)\,dz \right|
   \le \frac{1}{R^2 - 4}\cdot \pi R \xrightarrow[R\to\infty]{} 0 .$$
(The $1/R^2$ decay of $|f|$ makes this elementary; one does not even need Jordan's
lemma.)

**The residue.** The residue at the enclosed simple pole $z = 2i$ is
$$\operatorname*{Res}_{z=2i} f(z)
   = \frac{e^{it z}}{z + 2i}\bigg|_{z=2i}
   = \frac{e^{it(2i)}}{4i}
   = \frac{e^{-2t}}{4i}.$$
By the residue theorem,
$$\int_{-R}^{R} f(x)\,dx + \int_{C_R} f(z)\,dz
   = 2\pi i \cdot \frac{e^{-2t}}{4i} = \frac{\pi}{2}\,e^{-2t}.$$
Letting $R \to \infty$ and using that the arc integral vanishes,
$$\int_{-\infty}^{\infty} \frac{e^{itx}}{x^2+4}\,dx = \frac{\pi}{2}\,e^{-2t}
  \qquad (t \ge 0).$$
This value is real and positive, confirming that taking the real part above changed
nothing.

**Assembling the answer.** For $t \ge 0$,
$$I(t) = \frac{1}{2}\int_{-\infty}^{\infty}\frac{\cos(tx)}{x^2+4}\,dx
       = \frac{1}{2}\cdot \frac{\pi}{2}\,e^{-2t} = \frac{\pi}{4}\,e^{-2t}.$$
Since $I(t) = I(|t|)$ for all real $t$,
$$\boxed{\ \int_0^{\infty} \frac{\cos(tx)}{x^2+4}\,dx = \frac{\pi}{4}\,e^{-2|t|}\ }
  \qquad (t \in \R). \qquad \blacksquare$$

**Sanity checks.**

- *Value at $t = 0$.* Directly,
  $\int_0^{\infty}\frac{dx}{x^2+4} = \tfrac12 \arctan\!\frac{x}{2}\big|_0^{\infty}
  = \tfrac12\cdot\tfrac{\pi}{2} = \tfrac{\pi}{4}$, matching $\tfrac{\pi}{4}e^{0}$.

- *Parameter ODE cross-check.* Writing $J(t) = \int_{-\infty}^{\infty}
  \frac{\cos(tx)}{x^2+4}\,dx = \frac{\pi}{2}e^{-2|t|}$, one expects $J''(t) =
  4\,J(t)$ for $t \ne 0$, since formally $J''(t) = -\int \frac{x^2\cos(tx)}{x^2+4}
  = -\int\cos(tx) + 4\int\frac{\cos(tx)}{x^2+4}$ and the first (delta-like) term
  drops away from $t=0$. Indeed $\frac{d^2}{dt^2}\big(\frac{\pi}{2}e^{-2|t|}\big) =
  4\cdot\frac{\pi}{2}e^{-2|t|}$ for $t \ne 0$, with the kink at $t = 0$ reflecting
  the omitted delta — consistent with the contour result.

**Remark.** This is the case $a = 2$ of the standard Poisson-kernel transform
$\int_0^{\infty}\frac{\cos(tx)}{x^2+a^2}\,dx = \frac{\pi}{2a}e^{-a|t|}$ for $a > 0$;
the same upper-half-plane contour with pole at $z = ai$ gives the general formula
verbatim.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->


# APM m02A04: Large-t asymptotics of a Gaussian integral by completing the square

*(Sign note: as printed the exponent $t^3x^2+t^2x$ has a **positive** quadratic term, so
$e^{t^3x^2+t^2x}\to\infty$ as $x\to\pm\infty$ and the integral diverges for $t>0$. The
intended — convergent — integral, for which "complete the square / large $t$" is
meaningful, is $\displaystyle\int_{\mathbb R}e^{-t^3x^2+t^2x}\,dx$; this is what is solved
below. The result is the same to leading order for either sign of the linear term.)*

## Why It's Hard

The integral looks like a job for Laplace's method (asymptotic expansion around the
maximum of the exponent), but that machinery is overkill: because the exponent is exactly
quadratic in $x$, **completing the square turns it into an exact Gaussian**. The only
subtlety is keeping track of how the two different powers of $t$ — $t^3$ in the quadratic
term and $t^2$ in the linear term — combine: the maximum of the exponent is
$\frac{(t^2)^2}{4t^3}=\frac{t}{4}$, producing the exponential factor $e^{t/4}$, while the
Gaussian width contributes the algebraic prefactor $t^{-3/2}$. Reading off the *leading*
behavior means identifying which factor dominates (the exponential) and getting the
prefactor's power of $t$ exactly right.

## The Key Insight

Complete the square in $x$:
$$
-t^3x^2+t^2x=-t^3\Big(x-\tfrac{1}{2t}\Big)^2+\frac{t}{4}.
$$
The constant $\frac{t}{4}$ is the maximum value of the exponent; the remaining integral is
a pure Gaussian of "stiffness" $t^3$, contributing $\int e^{-t^3 u^2}\,du=\sqrt{\pi/t^3}$.
Hence the integral equals $e^{t/4}\sqrt{\pi}\,t^{-3/2}$ — exactly, not just asymptotically.

## Complete Proof

Consider $\displaystyle I(t)=\int_{\mathbb R}e^{-t^3x^2+t^2x}\,dx$ for $t>0$.

**Complete the square.** Factor out $-t^3$ from the $x$-dependent part:
$$
-t^3x^2+t^2x=-t^3\Big(x^2-\frac{t^2}{t^3}\,x\Big)=-t^3\Big(x^2-\frac{x}{t}\Big)
=-t^3\Big[\Big(x-\frac{1}{2t}\Big)^2-\frac{1}{4t^2}\Big].
$$
Distributing the $-t^3$,
$$
-t^3x^2+t^2x=-t^3\Big(x-\frac{1}{2t}\Big)^2+\frac{t^3}{4t^2}
=-t^3\Big(x-\frac{1}{2t}\Big)^2+\frac{t}{4}.
$$

**Evaluate the Gaussian.** Therefore
$$
I(t)=e^{t/4}\int_{\mathbb R}\exp\!\Big(-t^3\big(x-\tfrac{1}{2t}\big)^2\Big)\,dx .
$$
Substituting $u=x-\frac{1}{2t}$ (translation, $du=dx$) and using the standard Gaussian
integral $\int_{\mathbb R}e^{-au^2}\,du=\sqrt{\pi/a}$ with $a=t^3>0$,
$$
I(t)=e^{t/4}\sqrt{\frac{\pi}{t^3}}=\sqrt{\pi}\,\,t^{-3/2}\,e^{t/4}.
$$

**Leading-order large-$t$ behavior.** This expression is exact, and as $t\to\infty$ its
behavior is dominated by the exponential factor:
$$
\boxed{\ \int_{\mathbb R}e^{-t^3x^2+t^2x}\,dx=\sqrt{\pi}\;t^{-3/2}\,e^{t/4}
\ \sim\ \sqrt{\pi}\;t^{-3/2}e^{t/4}\quad(t\to\infty).\ }
$$
$\blacksquare$

### Remark

The computation is exact because the exponent is quadratic; Laplace's method would
reproduce the same answer (the maximizer is $x_*=\frac1{2t}$, the exponent maximum is
$\frac t4$, the second derivative is $-2t^3$, and Laplace gives $e^{t/4}\sqrt{2\pi/2t^3}=
\sqrt\pi t^{-3/2}e^{t/4}$ — identical, with no higher-order corrections precisely because
the phase has no cubic or higher terms). The scaling lesson: with a quadratic term
$\sim t^3$ and linear term $\sim t^2$, the "completed-square" peak height scales as
$(t^2)^2/t^3=t$, so the integral grows like $e^{t/4}$, and the curvature $t^3$ sets the
width $\sim t^{-3/2}$. If instead the printed sign $+t^3x^2$ is taken literally the
integral diverges; the leading-order question only makes sense for the convergent
(negative-definite) quadratic, treated above.

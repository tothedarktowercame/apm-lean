<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98A05: ∫₀^∞ dx/(1+x³) by a 120° pie-slice contour

## Why It's Hard

Over the reals this is a partial-fractions slog. Factoring
$1 + x^3 = (x+1)(x^2 - x + 1)$ and decomposing produces a logarithm plus an
$\arctan$ with irrational coefficients; evaluating the antiderivative from $0$ to
$\infty$ and watching the pieces cancel is error-prone and unenlightening.

The contour approach is far cleaner but only if you pick the *right* contour. The
usual semicircle trick fails: $\frac{1}{1+x^3}$ is **not even**, so closing across
the whole real line tells you nothing about $\int_0^\infty$ specifically, and the
negative real axis bears no simple relation to the positive one. The difficulty is
recognizing the symmetry that *is* present — a three-fold rotational one — and
exploiting it with a wedge rather than a disk. Then there are the usual hazards:
identifying which root of $z^3 = -1$ falls inside the wedge, computing the residue,
and — the step where signs and phases go to die — simplifying a complex constant
back down to the manifestly real answer.

## The Key Insight

The integrand has a rotational self-similarity tied to the angle $2\pi/3$. Rotating
$z$ by $e^{2\pi i/3}$ leaves $z^3$ fixed,
$$(e^{2\pi i/3}z)^3 = e^{2\pi i} z^3 = z^3,$$
so $\frac{1}{1+z^3}$ is invariant under that rotation. Consequently, if we integrate
over the boundary of the **pie slice of angle $2\pi/3$**, the integral back down the
slanted edge is just a constant multiple ($-e^{2\pi i/3}$, the rotation's Jacobian)
of the integral $I = \int_0^\infty \frac{dx}{1+x^3}$ out along the real edge. The
arc at radius $R$ contributes nothing as $R \to \infty$. So instead of the
even-function relation "boundary $= 2I$," we get "boundary $= (1 - e^{2\pi i/3})\,I$"
— and the residue theorem turns that into a *linear equation* for $I$. The wedge is
chosen exactly so that it captures **one** of the three poles of $\frac{1}{1+z^3}$,
namely $e^{i\pi/3}$.

## Complete Proof

**Claim.** $\displaystyle \int_0^{\infty} \frac{dx}{1+x^3} = \frac{2\pi}{3\sqrt{3}}
= \frac{2\pi\sqrt{3}}{9}.$

Let $f(z) = \dfrac{1}{1+z^3}$. Factoring as the hint suggests,
$$1 + z^3 = (z+1)(z^2 - z + 1),$$
the poles are the cube roots of $-1$: $z = -1 = e^{i\pi}$ and the roots
$\frac{1 \pm i\sqrt3}{2} = e^{\pm i\pi/3}$ of $z^2 - z + 1$. All are simple.

**The contour.** For $R > 1$ let $\Gamma_R$ be the boundary of the circular sector
("pie slice") of radius $R$ and opening angle $2\pi/3$, traversed counterclockwise:

- $C_1$: the real segment $z = x$, $x : 0 \to R$;
- $C_2$: the arc $z = Re^{i\theta}$, $\theta : 0 \to 2\pi/3$;
- $C_3$: the slanted edge $z = e^{2\pi i/3} r$, $r : R \to 0$ (back to the origin).

Among the three poles, only $e^{i\pi/3}$ (argument $\pi/3 \in (0, 2\pi/3)$) lies
inside $\Gamma_R$; the poles $e^{i\pi}$ and $e^{-i\pi/3} = e^{5i\pi/3}$ have arguments
$\pi$ and $5\pi/3$, both outside the wedge.

**The slanted edge reproduces $I$.** On $C_3$, with $z = e^{2\pi i/3} r$ we have
$z^3 = e^{2\pi i} r^3 = r^3$ and $dz = e^{2\pi i/3}\,dr$, so
$$\int_{C_3} f(z)\,dz
   = \int_{R}^{0} \frac{e^{2\pi i/3}}{1 + r^3}\,dr
   = -\,e^{2\pi i/3} \int_0^{R} \frac{dr}{1 + r^3}.$$
Meanwhile $\displaystyle \int_{C_1} f(z)\,dz = \int_0^{R}\frac{dx}{1+x^3}$.

**The arc vanishes.** On $C_2$, $|1 + z^3| \ge R^3 - 1$, and $C_2$ has length
$\frac{2\pi}{3}R$, so
$$\left| \int_{C_2} f(z)\,dz \right| \le \frac{(2\pi/3)\,R}{R^3 - 1}
   \xrightarrow[R\to\infty]{} 0.$$

**The residue.** At a simple pole $z_0$ of $\frac{1}{1+z^3}$,
$\operatorname{Res} = \frac{1}{(1+z^3)'}\big|_{z_0} = \frac{1}{3 z_0^2}$. At
$z_0 = e^{i\pi/3}$, $z_0^2 = e^{2i\pi/3}$, so
$$\operatorname*{Res}_{z=e^{i\pi/3}} f = \frac{1}{3 e^{2i\pi/3}}
   = \tfrac{1}{3} e^{-2i\pi/3}.$$
By the residue theorem, $\displaystyle \oint_{\Gamma_R} f\,dz
= 2\pi i \cdot \tfrac{1}{3} e^{-2i\pi/3} = \frac{2\pi i}{3}\,e^{-2i\pi/3}$ for every
$R > 1$.

**Solve for $I$.** Adding the three pieces and letting $R \to \infty$ (the arc drops
out, and $\int_0^R \to I$ on both straight edges):
$$\big(1 - e^{2\pi i/3}\big)\,I = \frac{2\pi i}{3}\,e^{-2i\pi/3}.$$
Use the identity $1 - e^{i\theta} = -2i\sin(\theta/2)\,e^{i\theta/2}$ with
$\theta = 2\pi/3$:
$$1 - e^{2\pi i/3} = -2i\sin\!\tfrac{\pi}{3}\,e^{i\pi/3}
   = -2i\cdot\tfrac{\sqrt3}{2}\,e^{i\pi/3} = -i\sqrt3\,e^{i\pi/3}.$$
Therefore
$$I = \frac{2\pi i}{3} \cdot \frac{e^{-2i\pi/3}}{-i\sqrt3\,e^{i\pi/3}}
    = \frac{2\pi i}{3} \cdot \frac{e^{-i\pi}}{-i\sqrt3}
    = \frac{2\pi i}{3} \cdot \frac{-1}{-i\sqrt3}
    = \frac{2\pi i}{3 i \sqrt3}
    = \frac{2\pi}{3\sqrt3}.$$
(Here $e^{-2i\pi/3}/e^{i\pi/3} = e^{-i\pi} = -1$.) Rationalizing,
$$\boxed{\ \int_0^{\infty}\frac{dx}{1+x^3} = \frac{2\pi}{3\sqrt3}
   = \frac{2\pi\sqrt3}{9}\ } \approx 1.2092. \qquad \blacksquare$$

**Sanity checks.**

- *General formula.* For $n \ge 2$, $\int_0^\infty \frac{dx}{1+x^n} =
  \dfrac{\pi/n}{\sin(\pi/n)}$. At $n = 3$ this is
  $\dfrac{\pi/3}{\sin(\pi/3)} = \dfrac{\pi/3}{\sqrt3/2} = \dfrac{2\pi}{3\sqrt3}$,
  agreeing with the boxed value.
- *Positivity / magnitude.* The integrand is positive and decays like $x^{-3}$, so
  the integral is a modest positive number; $1.21$ is consistent (e.g. the tail
  $\int_1^\infty x^{-3} = \tfrac12$ plus a sub-1 head).
- The final answer is real, as it must be — the imaginary unit cancels in the last
  step, which is the structural check that no phase error slipped in.

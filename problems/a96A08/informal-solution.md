## apm-a96A08 — An integral with two removable singularities

**Problem.** Evaluate $\int_{-\infty}^{\infty}\frac{\sin(\pi x)}{x^2-x}\,dx$, explaining every step.

**Answer: $-2\pi$.**

**The integral is not singular.** Write $x^2-x=x(x-1)$. Both apparent poles sit at integers, and $\sin(\pi x)$ vanishes at every integer, so both singularities are removable: near $x=0$ the integrand is $\frac{\pi x+O(x^3)}{x(x-1)}\to-\pi$, and near $x=1$, putting $u=x-1$, it is $\frac{-\pi u+O(u^3)}{u(u+1)}\to-\pi$. Extended by those two values the integrand is continuous on all of $\mathbb R$. For $|x|\ge 2$ we have $|x^2-x|\ge x^2/2$, so the integrand is bounded by $2/x^2$ and the integral converges absolutely at both ends. So the value below is an honest Lebesgue integral, not merely a principal value.

**Informal proof (partial fractions).** Since $\frac{1}{x(x-1)}=\frac{1}{x-1}-\frac{1}{x}$,
$$\frac{\sin(\pi x)}{x^2-x}=\frac{\sin(\pi x)}{x-1}-\frac{\sin(\pi x)}{x}.$$
The two pieces are each only conditionally integrable, so combine them under a common symmetric truncation $\int_{-R}^{R}$ and let $R\to\infty$ at the end.

For the second piece, $\int_{-\infty}^{\infty}\frac{\sin(\pi x)}{x}\,dx=\pi$, the Dirichlet integral (substituting $u=\pi x$ turns it into $\int_{-\infty}^{\infty}\frac{\sin u}{u}\,du=\pi$).

For the first, substitute $u=x-1$ and use $\sin(\pi(u+1))=-\sin(\pi u)$:
$$\int_{-\infty}^{\infty}\frac{\sin(\pi x)}{x-1}\,dx=\int_{-\infty}^{\infty}\frac{-\sin(\pi u)}{u}\,du=-\pi.$$

Hence the integral is $-\pi-\pi=-2\pi$.

**Check by contour integration.** Let $f(z)=\dfrac{e^{i\pi z}}{z(z-1)}$ and integrate over a large semicircle in the upper half-plane indented above the two real poles. Jordan's lemma kills the large arc, $f$ is analytic inside, and an indented contour picks up $\pi i$ times the residue at each real simple pole:
$$\mathrm{Res}_{z=0}f=\frac{e^{0}}{-1}=-1,\qquad \mathrm{Res}_{z=1}f=\frac{e^{i\pi}}{1}=-1.$$
So $\mathrm{P.V.}\int_{-\infty}^{\infty}\frac{e^{i\pi x}}{x^2-x}\,dx=\pi i(-1-1)=-2\pi i$, and taking imaginary parts gives $-2\pi$ again.

**Lean 4 statement:**

```lean
/-- apm-a96A08: the integral evaluates to -2π. -/
theorem apm_a96a08 :
    MeasureTheory.Integrable apm_a96A08_integrand ∧
      (∫ x : ℝ, apm_a96A08_integrand x ∂volume) = -(2 * Real.pi) := by
  sorry
```

**Mathlib cross-refs:** `Real.sinc`, `integral_sinc`, `MeasureTheory.Integrable`,
`intervalIntegral_tendsto_integral`, `integrableOn_Ioi_rpow_of_lt`.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96J03: The distributional Laplacian of the indicator of a ball is a dipole layer on the sphere

## Why It's Hard

The function `f = \chi_{B}` (indicator of the closed unit ball `B = \{\|x\| \le 1\}`) is **discontinuous**
across the unit sphere `S^{n-1} = \{\|x\| = 1\}`, so `\triangle f` cannot be an ordinary function — it must
be a *singular distribution concentrated on the sphere*. The difficulty is identifying *which* singular
object it is. A first guess of "some delta on the sphere" is wrong in a subtle way: because `f` has a jump
in its **value** (not in its normal derivative), the answer is not a single layer `\delta_S` but a
**double layer** (dipole) — the normal derivative of surface measure. Getting the type, the orientation,
and the normalization right is the whole challenge.

The clean path avoids trying to differentiate a discontinuous function twice by hand. Instead one uses the
*definition* of the distributional Laplacian — move both derivatives onto the test function,
`\langle \triangle f, \varphi\rangle = \langle f, \triangle\varphi\rangle` — and then collapses the
resulting integral over the ball to a boundary integral via the divergence theorem.

> (The problem statement's second condition "`f(x)=0` if `\|x\|>0`" is a typo for `\|x\|>1`; `f` is the
> indicator of the unit ball.)

## The Key Insight

By definition `\langle \triangle f, \varphi\rangle = \langle f, \triangle\varphi\rangle = \int_{\|x\|\le1}\triangle\varphi\,dx`,
and the divergence theorem turns the integral of `\triangle\varphi = \nabla\cdot\nabla\varphi` over the
ball into a flux through the sphere:

$$\int_{\|x\|\le 1} \triangle\varphi\,dx = \int_{S^{n-1}} \nabla\varphi\cdot\nu\,d\sigma = \int_{S^{n-1}} \frac{\partial\varphi}{\partial\nu}\,d\sigma,$$

where `\nu = x` is the outward unit normal on the unit sphere and `d\sigma` is `(n-1)`-dimensional surface
measure. So `\triangle f` is the distribution that integrates the **outward normal derivative** of `\varphi`
over the sphere — a **dipole (double) layer**, expressible as `\triangle f = -\nabla\cdot(\nu\,\delta_{S^{n-1}})`.
The dipole (rather than a single layer `\delta_S`) appears precisely because `f` jumps in value across `S`.

## Complete Proof

Let `f = \chi_B`, `B = \{x \in \mathbb R^n : \|x\| \le 1\}`, `S = S^{n-1} = \{\|x\| = 1\}`. `f` is bounded
and measurable, hence locally integrable, so it defines a distribution and `\triangle f` is defined by

$$\langle \triangle f, \varphi\rangle = \langle f, \triangle\varphi\rangle = \int_{\mathbb R^n} f\,\triangle\varphi\,dx
= \int_{\|x\|\le 1} \triangle\varphi(x)\,dx, \qquad \varphi \in C_c^\infty(\mathbb R^n).$$

**Divergence theorem on the ball.** Since `\triangle\varphi = \nabla\cdot(\nabla\varphi)`, the divergence
theorem on `B` (outward unit normal `\nu(x) = x` on `S`) gives

$$\int_{\|x\|\le 1} \triangle\varphi\,dx = \int_{B} \nabla\cdot(\nabla\varphi)\,dx
= \int_{S} \nabla\varphi\cdot\nu\,d\sigma = \int_{S} \frac{\partial\varphi}{\partial\nu}\,d\sigma,$$

where `\partial\varphi/\partial\nu = \nabla\varphi\cdot\nu` is the outward normal (radial) derivative on
the unit sphere. Therefore

$$\boxed{\ \langle \triangle f, \varphi\rangle = \int_{S^{n-1}} \frac{\partial\varphi}{\partial\nu}\,d\sigma
= \int_{\|x\|=1} \frac{\partial\varphi}{\partial r}\,d\sigma.\ }$$

`\triangle f` is the singular distribution supported on the unit sphere that pairs a test function with the
integral of its outward normal derivative over `S`.

**Equivalent forms.** Let `\delta_S` denote surface measure on `S` (`\langle \delta_S, \varphi\rangle = \int_S \varphi\,d\sigma`).
Computing the distributional gradient of `f`: for each `i`,
`\langle \partial_i f, \varphi\rangle = -\int_B \partial_i\varphi = -\int_S \varphi\,\nu_i\,d\sigma`, so

$$\nabla f = -\,\nu\,\delta_S \qquad (\nu = x \text{ the outward normal}),$$

a vector-valued single layer. Taking the divergence,
`\langle \triangle f, \varphi\rangle = \langle \nabla\cdot(\nabla f), \varphi\rangle = -\langle \nabla f, \nabla\varphi\rangle
= \int_S \nu\cdot\nabla\varphi\,d\sigma = \int_S \partial_\nu\varphi\,d\sigma`, consistent with the boxed
formula. Hence

$$\triangle f = -\,\nabla\cdot\big(\nu\,\delta_{S^{n-1}}\big),$$

the **double (dipole) layer** on the unit sphere.

**Check in `n = 1`.** Here `B = [-1,1]`, `f = H(x+1) - H(x-1)`, so `f'' = \delta'(x+1) - \delta'(x-1)`, which
pairs as `\langle f'', \varphi\rangle = \varphi'(1) - \varphi'(-1)`. The boxed formula gives
`\int_{S^0}\partial_\nu\varphi = \partial_\nu\varphi(1) + \partial_\nu\varphi(-1) = \varphi'(1) + (-\varphi'(-1)) = \varphi'(1) - \varphi'(-1)`
(outward normal is `+1` at `x=1`, `-1` at `x=-1`). The two agree. ∎

**Remark.** The result captures a general principle: differentiating an indicator `\chi_\Omega` once gives a
**single layer** `-\nu\,\delta_{\partial\Omega}` (the jump in *value* concentrated on the boundary, weighted
by the normal), and differentiating again gives a **double layer** `-\nabla\cdot(\nu\,\delta_{\partial\Omega})`
(a dipole). No `\delta_S` term proportional to surface measure appears in `\triangle f` because the
*normal-derivative* of `f` does not jump (`f` is locally constant on each side); only its value jumps,
which is exactly what produces a dipole rather than a monopole layer. The distributional Laplacian's
defining move — throw both derivatives onto `\varphi`, then apply the divergence theorem on the ball —
makes the whole computation a one-line boundary integral.

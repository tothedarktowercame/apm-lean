<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94A10: The inverse-square solid-angle form on ℝ³∖{0} is closed but not exact

## Why It's Hard

The form `\omega` looks forbidding, but it is the **flux form of the inverse-square field** `\vec F =
\vec r/r^3` (with `r=\sqrt{x^2+y^2+z^2}`), and the two claims test two different ideas:

- **Closed (`d\omega=0`)** is the fact that `\vec F` is **divergence-free away from the origin** — and the
  exponent `3/2` (i.e. the `r^{-2}` magnitude) is *exactly* the one that achieves this; any other power
  leaves a nonzero divergence. The computation requires care with `\partial r/\partial x=x/r` and the
  product rule, and the three terms must cancel precisely.
- **Not exact** is the genuine subtlety. One cannot prove non-exactness by *failing to find* a potential `\eta`
  (maybe you just didn't look hard enough — and on `\mathbb R^3` the Poincaré lemma would even guarantee
  one). The honest obstruction is **topological**: `\mathbb R^3\setminus\{0\}` is *not* contractible (it
  deformation-retracts onto `S^2`), so closed forms can fail to be exact. The detector is the **period**
  `\int_{S^2}\omega`: an exact form must integrate to `0` over the *closed* surface `S^2` by Stokes, but
  `\int_{S^2}\omega = 4\pi \ne 0`. Recognizing that a nonzero period *is* the proof of non-exactness is the
  key.

## The Key Insight

Write `\omega = \dfrac{x\,dy\wedge dz + y\,dz\wedge dx + z\,dx\wedge dy}{(x^2+y^2+z^2)^{3/2}}` (using
`-dx\wedge dz = dz\wedge dx`), the flux form of `\vec F=\vec r/r^3`.

- **Closed:** `d\omega = (\operatorname{div}\vec F)\,dx\wedge dy\wedge dz`, and
  `\operatorname{div}(\vec r/r^3)=0` for `r\ne0`.
- **Not exact:** over the unit sphere, `\omega` restricts to the solid-angle (area) form, so
  $$
  \int_{S^2}\omega = 4\pi \ne 0;
  $$
  but any exact form `d\eta` satisfies `\int_{S^2} d\eta=\int_{\partial S^2}\eta=0` (Stokes, `S^2` closed).
  Hence `\omega` is not exact.

## Complete Proof

On `\mathbb R^3\setminus\{0\}`, let `r=\sqrt{x^2+y^2+z^2}` and rewrite the form (using `-dx\wedge dz =
dz\wedge dx`) as
$$
\omega = P\,dy\wedge dz + Q\,dz\wedge dx + R\,dx\wedge dy, \qquad P=\frac{x}{r^3},\ Q=\frac{y}{r^3},\ R=\frac{z}{r^3}.
$$
This is the flux form of the vector field `\vec F=(P,Q,R)=\vec r/r^3`.

### `\omega` is closed

For a `2`-form `P\,dy\wedge dz + Q\,dz\wedge dx + R\,dx\wedge dy`, the exterior derivative is
$$
d\omega = \Big(\frac{\partial P}{\partial x}+\frac{\partial Q}{\partial y}+\frac{\partial R}{\partial z}\Big)\,dx\wedge dy\wedge dz = (\operatorname{div}\vec F)\,dx\wedge dy\wedge dz .
$$
Compute, using `\partial r/\partial x = x/r`:
$$
\frac{\partial}{\partial x}\Big(\frac{x}{r^3}\Big) = \frac{1}{r^3} + x\cdot(-3)r^{-4}\cdot\frac{x}{r} = \frac{1}{r^3} - \frac{3x^2}{r^5} = \frac{r^2-3x^2}{r^5},
$$
and symmetrically for the `y`- and `z`-derivatives. Summing,
$$
\operatorname{div}\vec F = \frac{(r^2-3x^2)+(r^2-3y^2)+(r^2-3z^2)}{r^5} = \frac{3r^2 - 3(x^2+y^2+z^2)}{r^5} = \frac{3r^2-3r^2}{r^5} = 0
$$
for all `r\ne0`. Hence `d\omega = 0`: **`\omega` is closed** on `\mathbb R^3\setminus\{0\}`.

### `\omega` is not exact

**Compute the period over `S^2`.** On the unit sphere `r=1`, the denominator is `1`, so `\omega` restricts to
$$
\omega\big|_{S^2} = x\,dy\wedge dz + y\,dz\wedge dx + z\,dx\wedge dy,
$$
the standard area (solid-angle) form. As a flux integral, `\int_{S^2}\omega = \int_{S^2}\vec F\cdot\vec n\,dA`
with `\vec n` the outward unit normal; on the unit sphere `\vec F=\vec r/1=\vec r` and `\vec n=\vec r`, so
`\vec F\cdot\vec n=|\vec r|^2=1` and
$$
\int_{S^2}\omega = \int_{S^2} 1\,dA = \operatorname{area}(S^2) = 4\pi \ne 0 .
$$

**Exact forms have zero period.** Suppose, for contradiction, that `\omega = d\eta` for some smooth `1`-form
`\eta` on `\mathbb R^3\setminus\{0\}`. The unit sphere `S^2\subset\mathbb R^3\setminus\{0\}` is a closed
surface (`\partial S^2=\varnothing`), so by **Stokes' theorem**,
$$
\int_{S^2}\omega = \int_{S^2} d\eta = \int_{\partial S^2}\eta = 0 .
$$
This contradicts `\int_{S^2}\omega = 4\pi\ne0`. Therefore **no such `\eta` exists**: `\omega` is closed but
**not exact**. ∎

**Remark.** The two halves expose the two faces of the same object. *Closedness* is the divergence-free
property of the inverse-square field, and the exponent `3/2` is the unique one making it so: for `\omega_a =
(x\,dy\wedge dz+\cdots)/r^{a}` one finds `\operatorname{div} = (3-a)/r^{a}`, which vanishes only for `a=3`.
*Non-exactness* is the topology of the punctured space: `\mathbb R^3\setminus\{0\}\simeq S^2` has
`H^2_{dR}\cong\mathbb R`, and `\omega` is (a multiple of) its generator, with `\int_{S^2}` the isomorphism to
`\mathbb R`. The nonzero period `4\pi` is precisely the de Rham class of `\omega`, the obstruction to a global
potential — physically, the flux of a unit point charge (Gauss's law), nonzero exactly because the source at
`0` has been removed from the domain. (Locally `\omega` *is* exact — on any simply connected region missing
the origin, like the complement of a ray, it has a potential, the solid-angle function — but no single
potential exists on all of `\mathbb R^3\setminus\{0\}`.)

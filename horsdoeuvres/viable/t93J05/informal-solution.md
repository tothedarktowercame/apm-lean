<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93J05: A closed 2-form integrates to zero over a closed surface

## Why It's Hard

Part (a) is a routine but error-prone exterior-derivative computation: one must rewrite `\omega` in the
standard basis `dy\wedge dz,\ dz\wedge dx,\ dx\wedge dy` (watching the sign on the `dx\wedge dz` term, since
`dx\wedge dz = -dz\wedge dx`), and then collect the single `dx\wedge dy\wedge dz` coefficient — which is the
divergence of the associated vector field. The payoff, and the trap if you miscompute, is that the divergence
**vanishes identically**, so `\omega` is closed.

Part (b) looks like a hard surface integral over an awkward composite surface (a cylinder capped by a
hemisphere), tempting a brute-force parametrization. The point of part (a) is to make that unnecessary: for a
**closed** form, Stokes collapses the integral over a closed surface to the integral of `d\omega = 0` over the
enclosed solid, giving `0` — and the precise dimensions of the surface are irrelevant. Recognizing that (a)
exists precisely to trivialize (b) is the key.

## The Key Insight

Write `\omega = P\,dy\wedge dz + Q\,dz\wedge dx + R\,dx\wedge dy` with `P = -x^2`, `Q = -2yz`,
`R = z^2 + 2xz + 4` (using `2yz\,dx\wedge dz = -2yz\,dz\wedge dx`). Then

$$d\omega = \Big(\frac{\partial P}{\partial x} + \frac{\partial Q}{\partial y} + \frac{\partial R}{\partial z}\Big)dx\wedge dy\wedge dz
= \big(-2x - 2z + (2z + 2x)\big)\,dx\wedge dy\wedge dz = 0.$$

So `\omega` is **closed**. Hence for any closed surface `S = \partial V` bounding a compact solid `V`,
Stokes' theorem gives

$$\int_S \omega = \int_V d\omega = \int_V 0 = 0.$$

The capsule `S` (cylindrical sides capped by the hemisphere) bounds such a solid, oriented outward by the
given convention at the apex `(0,0,2)`, so the integral is `0`.

## Complete Proof

On `\mathbb R^3`, `\omega = (z^2 + 2xz + 4)\,dx\wedge dy - x^2\,dy\wedge dz + 2yz\,dx\wedge dz`.

### (a) `d\omega`

Compute term by term (each `d(g\,\alpha) = dg\wedge\alpha`, and only the derivative "transverse" to the
`2`-form survives):

$$d\big[(z^2+2xz+4)\,dx\wedge dy\big] = \partial_z(z^2+2xz+4)\,dz\wedge dx\wedge dy = (2z+2x)\,dx\wedge dy\wedge dz,$$
$$d\big[-x^2\,dy\wedge dz\big] = -\partial_x(x^2)\,dx\wedge dy\wedge dz = -2x\,dx\wedge dy\wedge dz,$$
$$d\big[2yz\,dx\wedge dz\big] = (2z\,dy + 2y\,dz)\wedge dx\wedge dz = 2z\,dy\wedge dx\wedge dz = -2z\,dx\wedge dy\wedge dz,$$

using `dz\wedge dx\wedge dy = dx\wedge dy\wedge dz` and `dy\wedge dx\wedge dz = -dx\wedge dy\wedge dz`. Adding,

$$\boxed{\ d\omega = \big(2z + 2x - 2x - 2z\big)\,dx\wedge dy\wedge dz = 0.\ }$$

`\omega` is closed. (Equivalently, `\omega` is the flux form of `F = (-x^2, -2yz, z^2+2xz+4)`, and
`\operatorname{div} F = -2x - 2z + (2z+2x) = 0`.)

### (b) `\int_S \omega`

The surface `S` is the capsule consisting of the cylindrical wall `x^2+y^2 = 1` together with the
hemispherical cap `\{x^2+y^2+(z-1)^2 = 1,\ 1\le z\le 2\}` that closes its top (the cap's rim, the circle
`x^2+y^2=1` at `z=1`, lies on the cylinder). Taken as the boundary of the compact solid region `V` it
encloses, `S` is a closed oriented surface; the prescribed orientation (tangent plane at the apex `(0,0,2)`
identified with the `xy`-plane "in the obvious way") is the outward orientation `S = \partial V`.

Since `\omega` is closed by part (a), Stokes' theorem gives

$$\int_S \omega = \int_{\partial V}\omega = \int_V d\omega = \int_V 0 = 0.$$

$$\boxed{\ \int_S \omega = 0.\ }\qquad\blacksquare$$

**Remark.** Part (a) is engineered to make part (b) immediate: a *closed* form has zero integral over any
closed surface, by Stokes — no parametrization of the cylinder-plus-cap is needed, and the answer is `0`
independent of the surface's exact size. (For the integral to be well defined the surface must be compact and
closed; the literal "infinite cylinder `x^2+y^2=1`" is non-compact and would give a divergent integral from
the `-2z\sin^2\theta` term, so the well-posed reading is the bounded closed capsule above. If instead one
intends an *open* capped cylinder whose lower rim is the circle `x^2+y^2=1` at height `z=z_0`, closedness lets
one replace `S` by the flat disk there: on `z=z_0` only `R\,dx\wedge dy` survives, giving
`\int = (z_0^2+4)\pi` — e.g. `4\pi` for `z_0 = 0`. The clean closed-surface answer is `0`.) The general
principle: once `d\omega = 0`, surface integrals of `\omega` depend only on the boundary, and vanish when the
boundary is empty.

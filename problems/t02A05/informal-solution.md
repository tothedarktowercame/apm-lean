<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t02A05: Minimizing the flux of a 2-form over unit spheres via Stokes

## Why It's Hard

The problem asks to optimize a *surface* integral `\int_S \omega` over a whole family of unit spheres (one
for each center), then evaluate the minimum. Attacking the surface integral directly — parametrizing the
sphere and integrating the messy cubic `2`-form — is hopeless as an optimization, because the dependence on
the center is buried in the parametrization. The right move is **Stokes' theorem**, which converts the
boundary integral into a volume integral of `d\omega` over the enclosed ball; `d\omega` turns out to be a
clean positive *density* (the divergence of the associated vector field), and minimizing the total over
ball-position becomes a transparent "put the ball where the density is smallest" problem.

Two subtleties remain. First, the density `3(x-1)^2 + 3(y-2)^2 + 1` is a paraboloid in `x, y` but **constant
in `z`** (because the `z`-component of `\omega` is only *linear*, not cubic), so the minimizing center is not
a point but an entire *line* — the `z`-coordinate is free. Second, evaluating the minimum requires the
standard second moment `\int_{\text{ball}} u^2\,dV` of the unit ball, an easy but necessary spherical
integral.

## The Key Insight

By Stokes, `\int_S \omega = \int_B d\omega` where `B` is the unit ball bounded by `S` (outward orientation),
and

$$d\omega = \big[\,3(x-1)^2 + 3(y-2)^2 + 1\,\big]\,dx\wedge dy\wedge dz.$$

This density is `> 0` everywhere, so `\int_S \omega` is minimized by centering the ball where the density is
smallest. Its variable part `3(x-1)^2 + 3(y-2)^2` vanishes on the line `\{x = 1,\ y = 2\}` and has no
`z`-dependence, so the minimizing center is `(1, 2, c)` for **any** `c`. Centering there, the cross terms
integrate to zero and only the second moments survive:

$$\int_S \omega\big|_{\min} = \int_B \big[3u^2 + 3v^2 + 1\big]\,dV = 6\!\int_B u^2\,dV + \operatorname{Vol}(B)
= 6\cdot\tfrac{4\pi}{15} + \tfrac{4\pi}{3} = \frac{44\pi}{15}.$$

## Complete Proof

Let `\omega = (x-1)^3\,dy\wedge dz + (y-2)^3\,dz\wedge dx + (z-3)\,dx\wedge dy`, the flux form of the vector
field `F = \big((x-1)^3,\, (y-2)^3,\, (z-3)\big)`.

**Step 1 — Stokes.** For a unit sphere `S = \partial B` (`B` the unit ball it bounds, oriented as its
boundary),

$$\int_S \omega = \int_B d\omega.$$

Compute `d\omega` (equivalently `\operatorname{div} F\, dV`):

$$d\omega = 3(x-1)^2\,dx\wedge dy\wedge dz + 3(y-2)^2\,dy\wedge dz\wedge dx + 1\cdot dz\wedge dx\wedge dy
= \big[3(x-1)^2 + 3(y-2)^2 + 1\big]\,dV,$$

since `dy\wedge dz\wedge dx = dz\wedge dx\wedge dy = dx\wedge dy\wedge dz = dV`.

**Step 2 — Reduce the optimization.** Thus `\int_S \omega = \int_B \rho\,dV` with density
`\rho = 3(x-1)^2 + 3(y-2)^2 + 1 > 0`. Let the unit ball be centered at `(a, b, c)` and substitute centered
coordinates `u = x-a, v = y-b, w = z-c` (so `B = \{u^2+v^2+w^2 \le 1\}`). Then `x - 1 = u + (a-1)`, and
expanding,

$$\int_B (x-1)^2\,dV = \int_B \big[u^2 + 2(a-1)u + (a-1)^2\big]\,dV = \underbrace{\int_B u^2\,dV}_{=: I} + (a-1)^2\operatorname{Vol}(B),$$

because `\int_B u\,dV = 0` by symmetry. Similarly `\int_B (y-2)^2\,dV = I + (b-2)^2\operatorname{Vol}(B)`.
The constant `1` integrates to `\operatorname{Vol}(B)`. Therefore

$$\int_S \omega = 3\big[\,2I + \big((a-1)^2 + (b-2)^2\big)\operatorname{Vol}(B)\,\big] + \operatorname{Vol}(B)
= 6I + \operatorname{Vol}(B) + 3\operatorname{Vol}(B)\big[(a-1)^2 + (b-2)^2\big].$$

**Step 3 — Minimize.** The only center-dependence is the nonnegative term `3\operatorname{Vol}(B)[(a-1)^2 + (b-2)^2]`,
minimized (`= 0`) exactly when `a = 1` and `b = 2`; the coordinate `c` is **free**. So the minimizing spheres
are the unit spheres centered on the line

$$\boxed{\ \{(1, 2, c) : c \in \mathbb R\}\ }$$

(e.g. centered at `(1,2,3)`), reflecting that `\rho` has no `z`-dependence.

**Step 4 — Evaluate.** Compute the second moment of the unit ball. By symmetry
`\int_B u^2 = \int_B v^2 = \int_B w^2 = \tfrac13 \int_B r^2\,dV`, and

$$\int_B r^2\,dV = \int_0^1 r^2\cdot 4\pi r^2\,dr = 4\pi\int_0^1 r^4\,dr = \frac{4\pi}{5},
\quad\text{so}\quad I = \frac13\cdot\frac{4\pi}{5} = \frac{4\pi}{15}.$$

With `\operatorname{Vol}(B) = \tfrac{4\pi}{3}`, the minimum value is

$$\int_S \omega\big|_{\min} = 6I + \operatorname{Vol}(B) = 6\cdot\frac{4\pi}{15} + \frac{4\pi}{3}
= \frac{8\pi}{5} + \frac{4\pi}{3} = \frac{24\pi + 20\pi}{15} = \boxed{\dfrac{44\pi}{15}}.$$

∎

**Remark.** Stokes is the whole game: it turns a hard optimization over surfaces into "center the ball at the
minimum of a convex density." The asymmetry of `\omega` — cubic in `x, y` but only linear in `z` — is exactly
why the density `\rho = 3(x-1)^2 + 3(y-2)^2 + 1` is a paraboloid in `(x,y)` yet flat in `z`, producing a
one-parameter family of minimizers along the vertical line `x=1, y=2`. The minimum value `44\pi/15` is then a
routine spherical second-moment computation, and the constant `+1` (from `\partial_z(z-3)`) contributes the
fixed volume term `\tfrac{4\pi}{3}` no matter where the ball sits.

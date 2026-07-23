<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00A05: A closed-but-not-exact 1-form on ℝ³ minus the z-axis — its line integrals are winding numbers

## Why It's Hard

The form `ω = \dfrac{y}{x^2+y^2}dx - \dfrac{x}{x^2+y^2}dy + \cos z\,dz` looks like three unrelated terms,
and the temptation in (b) and (c) is to grind out the parametrized line integrals directly. That works for
`C_1` (a clean circle) but is hopeless for `C_2`, whose defining curve — the intersection of an ellipsoid
with an exponential graph — has no nice parametrization. The real difficulty is recognizing the
**structure**:

- The first two terms are (minus) the **angle form** `d\theta`, the standard generator of the de Rham
  cohomology of `ℝ^3 \setminus \{z\text{-axis}\}`. It is **closed but not exact**: `\theta = \operatorname{atan2}(y,x)`
  is only locally defined (multivalued, jumping by `2\pi` per loop around the `z`-axis), so `d\theta` is a
  genuine closed 1-form with no global potential.
- The last term `\cos z\,dz = d(\sin z)` is **exact**, with the *globally defined* potential `\sin z`.

Once `ω = -d\theta + d(\sin z)`, every line integral over a *closed* curve collapses: the exact piece
contributes `0`, and the angle piece contributes `-2\pi` times the **winding number of the curve about the
`z`-axis**. The only remaining work in (c) is the topological question "how many times does `C_2` wind?",
which is answered not by computation but by a *convexity* argument showing the curve encircles the axis
exactly once. Mistaking the form for exact (it integrates to `0`?) or trying to parametrize `C_2` are the
classic traps.

## The Key Insight

Split the form:
$$\omega = \underbrace{\frac{y\,dx - x\,dy}{x^2+y^2}}_{=\,-d\theta} \;+\; \underbrace{\cos z\,dz}_{=\,d(\sin z)} \;=\; -d\theta + d(\sin z),$$
where `\theta` is the polar angle in the `(x,y)`-plane. Hence `ω` is **closed** (`d\omega = 0`), and for any
*closed* curve `C` in `ℝ^3 \setminus \{z\text{-axis}\}`,
$$\int_C \omega = -\int_C d\theta + \underbrace{\int_C d(\sin z)}_{=\,0} = -2\pi\,(\text{winding number of } C \text{ about the }z\text{-axis}).$$
`C_1` winds once (counterclockwise) ⇒ `\int_{C_1}\omega = -2\pi`. For `C_2`, substituting the graph into the
ellipsoid gives a **convex** planar curve enclosing the origin once, so it too winds once ⇒
`\int_{C_2}\omega = -2\pi`. No parametrization of `C_2` is needed.

## Complete Proof

Work on `U = ℝ^3 \setminus \{z\text{-axis}\} = \{(x,y,z) : (x,y) \ne (0,0)\}`. Write `ω = P\,dx + Q\,dy + R\,dz`
with
$$P = \frac{y}{x^2+y^2}, \qquad Q = \frac{-x}{x^2+y^2}, \qquad R = \cos z.$$

### (a) `d\omega = 0`

For a 1-form in `ℝ^3`,
$$d\omega = \Big(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\Big)dx\wedge dy + \Big(\frac{\partial R}{\partial y} - \frac{\partial Q}{\partial z}\Big)dy\wedge dz + \Big(\frac{\partial P}{\partial z} - \frac{\partial R}{\partial x}\Big)dz\wedge dx.$$

Compute the partials (let `r^2 = x^2+y^2`):
$$
\frac{\partial Q}{\partial x} = \frac{\partial}{\partial x}\!\Big(\frac{-x}{x^2+y^2}\Big) = \frac{-(x^2+y^2) + x(2x)}{(x^2+y^2)^2} = \frac{x^2 - y^2}{(x^2+y^2)^2},
$$
$$
\frac{\partial P}{\partial y} = \frac{\partial}{\partial y}\!\Big(\frac{y}{x^2+y^2}\Big) = \frac{(x^2+y^2) - y(2y)}{(x^2+y^2)^2} = \frac{x^2 - y^2}{(x^2+y^2)^2}.
$$
So the `dx\wedge dy` coefficient is `\frac{x^2-y^2}{(x^2+y^2)^2} - \frac{x^2-y^2}{(x^2+y^2)^2} = 0`. Since
`R = \cos z` depends only on `z`, `\partial R/\partial y = \partial R/\partial x = 0`, and since `P, Q` are
independent of `z`, `\partial Q/\partial z = \partial P/\partial z = 0`; hence the `dy\wedge dz` and
`dz\wedge dx` coefficients also vanish. Therefore
$$
\boxed{\,d\omega = 0\,} \qquad\text{on } U .
$$

**Check.** The planar part is `\dfrac{y\,dx - x\,dy}{x^2+y^2} = -\dfrac{x\,dy - y\,dx}{x^2+y^2} = -d\theta`,
the negative of the standard (closed) angle form, and `\cos z\,dz = d(\sin z)` is exact. So
`ω = -d\theta + d(\sin z)` is a sum of two closed forms, confirming `d\omega = 0` independently. ∎

### (b) `\int_{C_1}\omega` over the unit circle in the `(x,y)`-plane

Parametrize `C_1` by `x = \cos t,\ y = \sin t,\ z = 0`, `t : 0 \to 2\pi` (counterclockwise). Then `dz = 0`,
so the `\cos z\,dz` term contributes nothing, and on `x^2+y^2 = 1`,
$$
\omega\big|_{C_1} = y\,dx - x\,dy = \sin t\,(-\sin t\,dt) - \cos t\,(\cos t\,dt) = -(\sin^2 t + \cos^2 t)\,dt = -dt .
$$
Hence
$$
\int_{C_1}\omega = \int_0^{2\pi} (-dt) = \boxed{-2\pi}.
$$
(Consistent with `\int_{C_1} -d\theta = -2\pi`, since `\theta` increases by `2\pi` over one counterclockwise
loop.)

### (c) `\int_{C_2}\omega` over the intersection of `2x^2+y^2+z^2 = 10` with `z = e^{y-x}`

`C_2` is a closed curve in `U` (we verify below it misses the `z`-axis). Use the decomposition
`ω = -d\theta + d(\sin z)` from (a):

**The exact part integrates to zero.** `\sin z` is a single-valued smooth function on `U`, so over the
closed curve `C_2`,
$$
\int_{C_2} d(\sin z) = 0
$$
(the fundamental theorem for line integrals: a closed loop returns to its start, and `\sin z` is
single-valued). Therefore
$$
\int_{C_2}\omega = -\int_{C_2} d\theta = -2\pi\cdot w,
$$
where `w` is the winding number of `C_2` about the `z`-axis — equivalently, the winding number about the
origin of the projection `\bar C_2` of `C_2` to the `(x,y)`-plane.

**The projection encircles the origin exactly once.** Substituting the graph `z = e^{y-x}` into the
ellipsoid equation, the projection `\bar C_2` is the planar curve
$$
g(x,y) := 2x^2 + y^2 + e^{2(y-x)} = 10 .
$$
The function `g` is **strictly convex** (it is a sum of the convex quadratic `2x^2+y^2` and the convex
function `e^{2(y-x)} = \exp(\text{linear})`), and `g(x,y) \to \infty` as `|(x,y)| \to \infty` (the term
`2x^2+y^2 \to \infty` while `e^{2(y-x)} \ge 0`). Hence the sublevel set `\{g \le 10\}` is a **bounded convex
region**. Since
$$
g(0,0) = 0 + 0 + e^{0} = 1 < 10,
$$
the origin lies in its *interior*. The boundary of a bounded convex region with the origin in its interior
is a single simple closed curve that encircles the origin exactly once; in particular it never passes
through the origin, so `C_2` indeed lies in `U` (avoids the `z`-axis). With the counterclockwise
orientation, the winding number is `w = +1`.

**Conclusion.**
$$
\int_{C_2}\omega = -2\pi \cdot 1 = \boxed{-2\pi}.
$$
∎

**Remark.** The phenomenon is exactly that `ω` is a *closed but not exact* form: its de Rham class is
`-[d\theta]`, the generator of `H^1_{dR}(ℝ^3\setminus\{z\text{-axis}\}) \cong \mathbb R`, while `\cos z\,dz`
is cohomologically trivial. Consequently `\int_C \omega` is a topological invariant of `C` — `-2\pi` times
its winding number about the `z`-axis — and is insensitive to the actual shape of the curve. That is why
the impossible-looking `C_2` gives the same answer as the unit circle `C_1`: both loop the axis once. Had
`C_2` *not* enclosed the axis (`w=0`), the integral would have been `0`.

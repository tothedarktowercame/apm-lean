<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t97J08: The angle form, and winding number as the integral of a pulled-back form

## Why It's Hard

The form `\alpha = (x\,dy - y\,dx)/2\pi` is the famous "angle form" in disguise, and the problem asks two
things that look computational but are really about **functoriality of pullback**. Part (a) wants an explicit
formula for `\beta = \varphi^*\hat\alpha` — a pullback through the radial projection `\varphi(z) = z/|z|` — and a
proof that it is closed. The temptation is to grind out `d\beta` by hand; the clean reason is that `\beta` is
the pullback of a `1`-form `\hat\alpha` living on the `1`-dimensional circle `S^1`, where `d\hat\alpha` is a
`2`-form and hence *automatically zero*. Part (b) is the real content: it identifies a **topological** quantity
(winding number `=` degree of `u = f/|f|`) with an **analytic** one (`\int_{S^1} f^*\beta`). The hurdle is to
see that the radial projection *composes* — `\varphi \circ f = u` — so that `f^*\beta = u^*\hat\alpha`, turning
the integral into the integral of the *normalized* angle form over `u`, which is exactly its degree. A side
trap: there is no global primitive for `\beta` (it is closed but **not exact** on `\mathbb C \setminus \{0\}`,
since `\int_{S^1}\beta = 1 \ne 0`), and that non-exactness is *precisely* what makes the winding number a
nontrivial invariant.

## The Key Insight

On `\mathbb C \setminus \{0\}`, `\varphi^*\hat\alpha` is the **normalized angle form**:

$$\boxed{\ \beta = \frac{x\,dy - y\,dx}{2\pi(x^2 + y^2)} = \frac{d\theta}{2\pi}.\ }$$

It is closed because `\beta = \varphi^*\hat\alpha` and `\hat\alpha` is a `1`-form on the `1`-manifold `S^1`, so
`d\hat\alpha = 0` forces `d\beta = \varphi^*(d\hat\alpha) = 0`. For (b), the single identity
`\varphi \circ f = f/|f| = u` gives

$$f^*\beta = f^*\varphi^*\hat\alpha = (\varphi\circ f)^*\hat\alpha = u^*\hat\alpha,$$

and since `\hat\alpha = d\theta/2\pi` is the generator of `H^1(S^1)` with `\int_{S^1}\hat\alpha = 1`, its
pullback integrates to the degree:

$$\int_{S^1} f^*\beta = \int_{S^1} u^*\hat\alpha = \deg u = W(f,0).$$

## Complete Proof

### (a) Formula for `\beta` and closedness

On `S^1`, use coordinates `(X,Y)` with `X^2 + Y^2 = 1`; then `\hat\alpha = (X\,dY - Y\,dX)/2\pi`. The projection
is `\varphi(x,y) = (x/r,\ y/r)` with `r = \sqrt{x^2+y^2}`, so under `\varphi` the pulled-back coordinate
functions are `X\circ\varphi = x/r`, `Y\circ\varphi = y/r`. Writing `u = x/r`, `v = y/r`,

$$\beta = \varphi^*\hat\alpha = \frac{u\,dv - v\,du}{2\pi}.$$

Compute `du = \dfrac{dx}{r} - \dfrac{x}{r^2}\,dr` and `dv = \dfrac{dy}{r} - \dfrac{y}{r^2}\,dr`, with
`dr = (x\,dx + y\,dy)/r`. Then

$$u\,dv - v\,du = \frac{x}{r}\Big(\frac{dy}{r} - \frac{y}{r^2}dr\Big) - \frac{y}{r}\Big(\frac{dx}{r} - \frac{x}{r^2}dr\Big) = \frac{x\,dy - y\,dx}{r^2} - \underbrace{\frac{xy}{r^3}dr + \frac{xy}{r^3}dr}_{=\,0},$$

so the `dr` terms cancel and

$$\boxed{\ \beta = \frac{x\,dy - y\,dx}{2\pi(x^2 + y^2)} = \frac{d\theta}{2\pi}\ } \qquad (\theta = \arg z).$$

**Closed.** Slickly: `\hat\alpha` is a `1`-form on the `1`-manifold `S^1`, so `d\hat\alpha` is a `2`-form on a
`1`-dimensional manifold, hence `d\hat\alpha = 0`; therefore `d\beta = d(\varphi^*\hat\alpha) = \varphi^*(d\hat\alpha) = 0`.
Directly, with `\beta = P\,dx + Q\,dy`, `P = \dfrac{-y}{2\pi r^2}`, `Q = \dfrac{x}{2\pi r^2}`,

$$\frac{\partial Q}{\partial x} = \frac{y^2 - x^2}{2\pi r^4} = \frac{\partial P}{\partial y}, \qquad\text{so}\qquad d\beta = \Big(\frac{\partial Q}{\partial x} - \frac{\partial P}{\partial y}\Big)dx\wedge dy = 0$$

on `\mathbb C \setminus \{0\}`. (Note `\int_{S^1}\beta = \int_0^{2\pi} d\theta/2\pi = 1 \ne 0`, so `\beta` is
closed but **not exact** — it generates `H^1_{dR}(\mathbb C\setminus\{0\}) \cong \mathbb R`.)

### (b) `W(f,0) = \int_{S^1} f^*\beta`

Let `f : S^1 \to \mathbb C\setminus\{0\}` be smooth and `u = f/|f| : S^1 \to S^1`, so `W(f,0) = \deg u` by
definition. The radial projection composes with `f`:

$$\varphi \circ f = \frac{f}{|f|} = u.$$

By naturality of pullback (and `\beta = \varphi^*\hat\alpha`),

$$f^*\beta = f^*\varphi^*\hat\alpha = (\varphi\circ f)^*\hat\alpha = u^*\hat\alpha.$$

Hence it remains to show `\int_{S^1} u^*\hat\alpha = \deg u`. Recall `\hat\alpha = d\theta/2\pi`. Parametrize the
domain circle by `t \in [0,1]`, `z = e^{2\pi i t}`, and lift `u` through the universal cover: write
`u(t) = e^{2\pi i\, U(t)}` for a smooth `U : [0,1] \to \mathbb R` with

$$U(1) - U(0) = \deg u \in \mathbb Z$$

(this integer is the definition of the degree of a circle map). The target angle coordinate of `u(t)` is
`2\pi U(t)`, so `u^*(d\theta) = d(2\pi U) = 2\pi\, U'(t)\,dt`, giving `u^*\hat\alpha = u^*(d\theta)/2\pi = U'(t)\,dt`.
Therefore

$$\int_{S^1} u^*\hat\alpha = \int_0^1 U'(t)\,dt = U(1) - U(0) = \deg u.$$

Combining,

$$\boxed{\ \int_{S^1} f^*\beta = \int_{S^1} u^*\hat\alpha = \deg u = W(f,0).\ } \qquad \blacksquare$$

**Remark.** This is the de Rham incarnation of winding number. The generator `\beta = d\theta/2\pi` of
`H^1_{dR}(\mathbb C\setminus\{0\})` is *engineered* to integrate to `1` over the unit circle; pulling it back by
`f` and integrating counts how many times `f` wraps around `0`. Two structural facts carry everything: pullback
is functorial (`(\varphi\circ f)^* = f^*\varphi^*`), which collapses `f^*\beta` to `u^*\hat\alpha` and discards
the radial (`|f|`) information automatically; and the integral of a pulled-back normalized volume form on a
closed manifold equals the degree (`\int_M u^*\omega = (\deg u)\int_N \omega`), here specialized to the circle.
The closedness of `\beta` is what makes `\int_{S^1} f^*\beta` a *homotopy invariant* of `f` — deform `f` and the
integral does not change — which is the analytic shadow of "degree is a homotopy invariant."

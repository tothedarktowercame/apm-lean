<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94A01: Second-order accuracy of the five-point discrete Laplacian

## Why It's Hard

The five-point operator `T` divides a difference of `u`-values by `h^2`, so before you can
claim it approximates `\triangle u` you must show that *every* term of size `1`, `h`, and even
the `h^2`-error candidates conspire to cancel, leaving an error that is genuinely `O(h^2)` after
the division. A careless expansion that stops too early will either miss the cancellation of the
odd-order terms or mis-locate the surviving term, and dividing by `h^2` *amplifies* any
mistake by two orders. The accuracy is "second order" only because of an exact cancellation, and
you have to expose that cancellation rather than assume it.

The second subtlety is the hypothesis. The problem assumes `u_{xxxx}` and `u_{yyyy}` are
**continuous**, not merely that they exist. Continuity is exactly what lets you (i) write a
Taylor expansion with a controllable fourth-order Lagrange remainder, and (ii) collapse two
remainder evaluations into one via the intermediate value theorem, and (iii) bound the result
by a finite constant. Existence of the fourth derivative alone would not give a clean uniform
bound.

## The Key Insight

The stencil is **centered and symmetric**: it pairs `u(x+h,y)` with `u(x-h,y)` and `u(x,y+h)`
with `u(x,y-h)`. In each pair, the odd-order Taylor terms (`\pm h u_x`, `\pm h^3 u_{xxx}/6`,
\dots) have opposite signs and **cancel**, while the even-order terms double. So a one-dimensional
centered second difference satisfies

$$u(x+h,y) + u(x-h,y) - 2u(x,y) = h^2 u_{xx} + \frac{h^4}{12}\,u_{xxxx}(\xi,y),$$

with the fourth derivative carrying the *entire* error. Adding the `x`- and `y`-pairs and
dividing by `h^2` turns this `h^4` remainder into an `h^2` error:

$$Tu = \triangle u + \frac{h^2}{12}\big[u_{xxxx}(\xi,y) + u_{yyyy}(x,\eta)\big].$$

The `1/h^2` normalization is the whole story: it is calibrated to leave `\triangle u` exact and
demote the leading `h^4` remainder to `h^2`. Continuity of the fourth derivatives makes the
bracket bounded, giving `Ch^2`.

## Complete Proof

Fix `(x,y)` and assume `u` is `C^4` in a neighborhood containing the closed stencil (the
horizontal and vertical segments of half-length `h` through `(x,y)`), with `u_{xxxx}` and
`u_{yyyy}` continuous there.

**Step 1 — One-dimensional centered second difference.** Apply Taylor's theorem in the
`x`-direction with Lagrange remainder of order four: there exist `\theta_1,\theta_2\in(0,1)` with

$$u(x\pm h, y) = u \pm h\,u_x + \frac{h^2}{2}u_{xx} \pm \frac{h^3}{6}u_{xxx}
+ \frac{h^4}{24}\,u_{xxxx}(x\pm\theta_{i}h,\,y),$$

(all undifferentiated terms evaluated at `(x,y)`). Adding the `+h` and `-h` expansions, the odd
terms cancel:

$$u(x+h,y) + u(x-h,y) - 2u(x,y) = h^2 u_{xx}
+ \frac{h^4}{24}\big[u_{xxxx}(x+\theta_1 h, y) + u_{xxxx}(x-\theta_2 h, y)\big].$$

Since `u_{xxxx}(\cdot,y)` is continuous, the intermediate value theorem gives a point `\xi`
between `x-h` and `x+h` with
`u_{xxxx}(x+\theta_1 h,y) + u_{xxxx}(x-\theta_2 h,y) = 2\,u_{xxxx}(\xi,y)`, hence

$$u(x+h,y) + u(x-h,y) - 2u(x,y) = h^2 u_{xx} + \frac{h^4}{12}\,u_{xxxx}(\xi,y). \tag{1}$$

**Step 2 — The `y`-direction is identical.** The same argument in `y` yields, for some `\eta`
between `y-h` and `y+h`,

$$u(x,y+h) + u(x,y-h) - 2u(x,y) = h^2 u_{yy} + \frac{h^4}{12}\,u_{yyyy}(x,\eta). \tag{2}$$

**Step 3 — Assemble `Tu`.** By definition,
`Tu = \big[(u(x+h,y)+u(x-h,y)-2u) + (u(x,y+h)+u(x,y-h)-2u)\big]/h^2`. Substituting (1) and (2)
and dividing by `h^2`,

$$Tu = u_{xx} + u_{yy} + \frac{h^2}{12}\big[u_{xxxx}(\xi,y) + u_{yyyy}(x,\eta)\big]
= (\triangle u)(x,y) + \frac{h^2}{12}\big[u_{xxxx}(\xi,y) + u_{yyyy}(x,\eta)\big].$$

**Step 4 — The error bound.** Therefore

$$(\triangle u)(x,y) - (Tu)(x,y) = -\frac{h^2}{12}\big[u_{xxxx}(\xi,y) + u_{yyyy}(x,\eta)\big].$$

Let `M = \sup\{|u_{xxxx}|,\,|u_{yyyy}|\}` over the (compact) neighborhood of `(x,y)` containing
the stencil — finite because the fourth derivatives are continuous there. Then

$$\boxed{\ |(\triangle u)(x,y) - (Tu)(x,y)| \le \frac{h^2}{12}\big(|u_{xxxx}(\xi,y)| + |u_{yyyy}(x,\eta)|\big)
\le \frac{2M}{12}\,h^2 = C h^2,\quad C = \frac{M}{6}. \ }$$

This is the claimed bound `|(\triangle u) - (Tu)| \le C h^2`, with the constant
`C = \tfrac16\max(\sup|u_{xxxx}|,\sup|u_{yyyy}|)` (equivalently
`C = \tfrac1{12}(\sup|u_{xxxx}| + \sup|u_{yyyy}|)`). The five-point Laplacian is second-order
accurate. ∎

**Remark.** The result is sharp in order: for `u(x,y)=x^4` the error is exactly
`\tfrac{h^2}{12}\,u_{xxxx} = \tfrac{h^2}{12}\cdot 24 = 2h^2 \ne o(h^2)`, so the exponent `2`
cannot be improved. Over a fixed bounded domain on which `u\in C^4`, the constant `C` is uniform,
giving a global `O(h^2)` discretization error — the basis for the second-order convergence of the
standard finite-difference Poisson solver.

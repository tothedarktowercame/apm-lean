<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99J02: A Green's function from two solutions — derivative jump, Wronskian, and Abel's identity

## Why It's Hard

The function `g_y` is built by gluing two different smooth formulas along the diagonal `x = y`, so its
distributional second derivative is not just the naive piecewise second derivative — gluing produces
boundary contributions at `x = y`. The first subtlety is to see *which* singular term appears: `g_y` turns
out to be **continuous** across `x = y` (the two formulas agree there), but its first derivative **jumps**.
Continuity kills any `\delta'` term, so `\partial_x^2 g_y` contributes exactly one Dirac mass, weighted by
the size of the derivative jump — and that jump is precisely the **Wronskian** of `u_1, u_2`. Getting the
type (`\delta`, not `\delta'`) and the coefficient right is the whole content of part (a).

Part (b) then asks why the result is the Green's function of `L = \tfrac{d^2}{dx^2} + q`, i.e. why
`Lg_y = c\,\delta_y` with `c` **independent of `y`**. Two facts must combine: the classical (non-singular)
part of `Lg_y` *vanishes* because each branch of `g_y` is a genuine solution of `u'' + qu = 0`; and the
remaining delta coefficient — the Wronskian — is *constant in `y`* by **Abel's identity**, which holds
exactly because the equation has no first-derivative term.

## The Key Insight

Write `W(t) = u_1(t)u_2'(t) - u_1'(t)u_2(t)` for the Wronskian. Then:

- `g_y` is **continuous** at `x = y` (both pieces give `u_1(y)u_2(y)`), but `\partial_x g_y` jumps there by
  `g_y'(y^+) - g_y'(y^-) = u_2'(y)u_1(y) - u_1'(y)u_2(y) = W(y)`.
- For a continuous, piecewise-`C^2` function, the distributional second derivative is
  `\{g_y''\} + [\partial_x g_y]\,\delta_y` — classical second derivative plus (jump of first derivative)
  times `\delta_y`. So `\partial_x^2 g_y = \{g_y''\} + W(y)\,\delta_y` (no `\delta'`, thanks to continuity).
- When `u_i'' + qu_i = 0`, each branch satisfies `\{g_y''\} + q g_y = 0` off the diagonal, leaving
  `Lg_y = W(y)\,\delta_y`. And **Abel's identity** gives `W' = u_1 u_2'' - u_1'' u_2 = -q u_1 u_2 + q u_1 u_2 = 0`,
  so `W` is the constant `c` — independent of `y`.

## Complete Proof

For fixed `y`, view `g_y` as a function of `x`:
`g_y(x) = u_1(x)u_2(y)` for `x \le y`, and `g_y(x) = u_2(x)u_1(y)` for `x \ge y`.

### (a) The distributional second derivative

**Continuity at `x = y`.** From the left, `g_y(y) = u_1(y)u_2(y)`; from the right, `g_y(y) = u_2(y)u_1(y)`.
These agree, so `g_y` is **continuous** at `x = y` (and clearly `C^2` away from it).

**First derivative and its jump.** Differentiating each branch in `x`:

$$g_y'(x) = \begin{cases} u_1'(x)u_2(y), & x < y, \\ u_2'(x)u_1(y), & x > y.\end{cases}$$

At `x = y` the one-sided derivatives are `g_y'(y^-) = u_1'(y)u_2(y)` and `g_y'(y^+) = u_2'(y)u_1(y)`, so the
jump is

$$\big[\partial_x g_y\big] := g_y'(y^+) - g_y'(y^-) = u_2'(y)u_1(y) - u_1'(y)u_2(y)
= u_1(y)u_2'(y) - u_1'(y)u_2(y) = W(y).$$

**Distributional second derivative.** For a continuous function that is `C^2` on each side of `y` with a
jump `[\partial_x g_y]` in the first derivative, integration by parts twice against a test function `\varphi`
(the boundary terms from the value cancel by continuity, those from the derivative produce the delta) gives

$$\boxed{\ \frac{\partial^2 g_y}{\partial x^2} = \{g_y''\} + W(y)\,\delta_y \ }$$

where `\{g_y''\}` is the classical second derivative off the diagonal,

$$\{g_y''\}(x) = \begin{cases} u_1''(x)\,u_2(y), & x < y, \\ u_2''(x)\,u_1(y), & x > y,\end{cases}$$

and `W(y) = u_1(y)u_2'(y) - u_1'(y)u_2(y)`. (Equivalently, for any test `\varphi`,
`\langle \partial_x^2 g_y, \varphi\rangle = \int \{g_y''\}\varphi\,dx + W(y)\varphi(y)`.) No `\delta'`
appears because `g_y` is continuous. ∎

### (b) `\partial_x^2 g_y + q\,g_y = c\,\delta_y`

Now assume `u_1'' + q u_1 = 0` and `u_2'' + q u_2 = 0`. From part (a),

$$\frac{\partial^2 g_y}{\partial x^2} + q\,g_y = \{g_y''\} + q\,g_y + W(y)\,\delta_y.$$

**The classical part cancels.** Off the diagonal, `q g_y` is an ordinary function and (using `u_i'' = -q u_i`):

$$x < y:\quad \{g_y''\} + q g_y = u_1''(x)u_2(y) + q(x)u_1(x)u_2(y) = \big(u_1'' + q u_1\big)(x)\,u_2(y) = 0,$$
$$x > y:\quad \{g_y''\} + q g_y = \big(u_2'' + q u_2\big)(x)\,u_1(y) = 0.$$

So `\{g_y''\} + q g_y = 0` as a function (hence as a distribution, with no extra delta from the regular term
`q g_y`). Therefore

$$\frac{\partial^2 g_y}{\partial x^2} + q\,g_y = W(y)\,\delta_y.$$

**The Wronskian is constant (Abel).** Differentiating `W = u_1 u_2' - u_1' u_2` and using `u_i'' = -q u_i`,

$$W'(y) = u_1 u_2'' - u_1'' u_2 = u_1(-q u_2) - (-q u_1)u_2 = -q u_1 u_2 + q u_1 u_2 = 0,$$

so `W` is a **constant**, say `c = u_1 u_2' - u_1' u_2` (independent of `y`). Hence

$$\boxed{\ \frac{\partial^2 g_y}{\partial x^2} + q\,g_y = c\,\delta_y, \qquad c = W = u_1 u_2' - u_1' u_2 \ \text{(constant)}.\ }\qquad\blacksquare$$

**Remark.** This is the construction of the **Green's function** for the Sturm–Liouville operator
`L = \tfrac{d^2}{dx^2} + q`: glue the solution `u_1` (controlling `x \le y`) to the solution `u_2`
(controlling `x \ge y`) so that the result is continuous, and the unavoidable *jump in the derivative*
generates a point impulse `c\,\delta_y`. The two structural facts are that each side solves the homogeneous
equation (killing the regular part of `Lg_y`) and that the impulse strength is the Wronskian, which Abel's
identity pins as a constant because the equation lacks a first-order term. Dividing by `c` (nonzero iff
`u_1, u_2` are independent) gives the true Green's function `G_y = g_y/c` with `LG_y = \delta_y`.

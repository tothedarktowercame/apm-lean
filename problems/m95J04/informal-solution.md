<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95J04: A nonlinear BVP by Green's-function contraction, and symmetry forced by uniqueness

## Why It's Hard

The boundary value problem `x'' = f(t,x)`, `x(0)=x(1)=0`, is nonlinear, so there is no closed form and
the linear toolkit does not apply directly. The standard move is to invert the linear part using the
Green's function `G` and recast the problem as a fixed point of the integral operator
`(Tx)(t) = -\int_0^1 G(t,s)f(s,x(s))\,ds`. But whether `T` contracts depends on a **sharp constant**:
you must compute `\max_t \int_0^1 G(t,s)\,ds` exactly, because the Lipschitz hypothesis `|f(t,u)-f(t,v)| \le 7.99\,|u-v|`
is calibrated to sit *just below* the threshold where contraction fails. The number `7.99` is not
arbitrary — it is a hair under `8 = 1/\max_t\int_0^1 G\,ds`, and missing the exact value `1/8` means
missing the whole point.

Part (b) hides a second, more elegant difficulty. Beyond checking the Lipschitz bound for the specific
`f`, one must prove the solution is *symmetric*, `x(t) = x(1-t)`. There is no formula for `x` to inspect;
the symmetry must be deduced **abstractly** from a symmetry of the equation together with **uniqueness** —
the insight that a unique solution must inherit any symmetry the problem possesses.

## The Key Insight

**(a)** The Green's function is nonnegative and integrates to

$$\int_0^1 G(t,s)\,ds = \frac{t(1-t)}{2}, \qquad \max_{t\in[0,1]} \int_0^1 G(t,s)\,ds = \frac{1}{8}\ \text{(at } t=\tfrac12).$$

So `\|Tx - Ty\|_\infty \le L \cdot \tfrac18 \|x-y\|_\infty`, and with `L = 7.99 < 8` the factor `L/8 < 1`
makes `T` a **contraction** — Banach's theorem gives a unique fixed point. The threshold is exactly `8`.

**(b)** For `f(t,x) = \sin(x-t)\sin(x+t-1)`, the partial derivative telescopes:
`\partial_x f = \sin\big((x-t)+(x+t-1)\big) = \sin(2x-1)`, bounded by `1`, so `f` is Lipschitz with
constant `1 \le 7.99` — part (a) applies. For the symmetry, `f` is invariant under `t \mapsto 1-t`:
`f(1-t,u) = f(t,u)`. Hence `y(t) := x(1-t)` solves the **same** BVP, so by uniqueness `y = x`, i.e.
`x(t) = x(1-t)`. Uniqueness transfers the equation's symmetry to its solution.

## Complete Proof

### (a) Existence and uniqueness

Work in `X = C[0,1]` with the sup norm. With the given Green's function
`G(t,s) = t(1-s)` for `t \le s`, `= s(1-t)` for `t \ge s` (`G \ge 0` on `[0,1]^2`), define

$$(Tx)(t) = -\int_0^1 G(t,s)\,f(s, x(s))\,ds.$$

By the stated equivalence, `x \in X` solves the BVP iff `Tx = x`. Since `f` is continuous, `Tx \in C[0,1]`
(indeed `C^2`), so `T : X \to X`.

**The key integral.** Fix `t` and split at `s = t`:

$$\int_0^1 G(t,s)\,ds = \int_0^t s(1-t)\,ds + \int_t^1 t(1-s)\,ds
= (1-t)\frac{t^2}{2} + t\frac{(1-t)^2}{2} = \frac{t(1-t)}{2}\big[t + (1-t)\big] = \frac{t(1-t)}{2}.$$

This is maximized at `t = \tfrac12`, giving `\max_t \int_0^1 G(t,s)\,ds = \tfrac{1/4}{2} = \tfrac18`.

**Contraction.** For `x, y \in X`, using `G \ge 0` and the Lipschitz bound `|f(s,u)-f(s,v)| \le L|u-v|`
with `L = 7.99`,

$$|(Tx)(t) - (Ty)(t)| \le \int_0^1 G(t,s)\,|f(s,x(s)) - f(s,y(s))|\,ds
\le L\,\|x-y\|_\infty \int_0^1 G(t,s)\,ds \le \frac{L}{8}\,\|x-y\|_\infty.$$

Taking the supremum over `t`,

$$\|Tx - Ty\|_\infty \le \frac{L}{8}\,\|x-y\|_\infty = \frac{7.99}{8}\,\|x-y\|_\infty, \qquad \frac{7.99}{8} < 1.$$

So `T` is a contraction on the complete space `C[0,1]`. By the **Banach fixed-point theorem** it has a
unique fixed point `x \in C[0,1]`, which is the unique solution of the BVP (and is `C^2`, by the integral
equation with `f` continuous). ∎

(The bound is sharp in form: `\tfrac18` is the exact operator constant, so the method works for any
Lipschitz constant `L < 8`; `7.99` is chosen to sit just inside this window.)

### (b) The specific equation and its symmetry

Let `f(t,x) = \sin(x-t)\sin(x+t-1)`, continuous on `[0,1]\times\mathbb R`.

**Lipschitz check.** Differentiating in `x` and using the angle-addition formula with `A = x-t`,
`B = x+t-1`,

$$\partial_x f = \cos(x-t)\sin(x+t-1) + \sin(x-t)\cos(x+t-1) = \sin\big((x-t)+(x+t-1)\big) = \sin(2x-1).$$

Hence `|\partial_x f| = |\sin(2x-1)| \le 1`, so by the mean value theorem
`|f(t,u) - f(t,v)| \le 1\cdot|u-v| \le 7.99\,|u-v|`. The hypothesis of part (a) holds (with room to spare),
so the BVP `x'' = \sin(x-t)\sin(x+t-1)`, `x(0)=x(1)=0`, has a **unique solution** `x`.

**Symmetry of `f` under `t \mapsto 1-t`.** Compute

$$f(1-t, x) = \sin\big(x-(1-t)\big)\sin\big(x+(1-t)-1\big) = \sin(x+t-1)\,\sin(x-t) = f(t,x),$$

so `f(1-t,u) = f(t,u)` for all `t, u` (the two sine factors simply swap).

**Symmetry of the solution.** Define `y(t) = x(1-t)`. Then `y(0) = x(1) = 0`, `y(1) = x(0) = 0`, and by
the chain rule `y''(t) = x''(1-t)`. Using the equation for `x` and then the symmetry of `f`,

$$y''(t) = x''(1-t) = f\big(1-t,\, x(1-t)\big) = f\big(1-t,\, y(t)\big) = f\big(t,\, y(t)\big).$$

Thus `y` satisfies the **same** BVP: `y'' = f(t,y)`, `y(0) = y(1) = 0`. By the uniqueness established in
part (a) (the Lipschitz constant `1 < 8`), `y = x`. Therefore

$$\boxed{\ x(t) = x(1-t) \quad \text{for all } t \in [0,1],\ }$$

i.e. the solution is symmetric about `t = \tfrac12`. ∎

**Remark.** Two ideas carry the problem. First, inverting the linear operator by the Green's function
turns the BVP into a fixed point whose contraction constant is the *exact* number `\tfrac18` — which is
why the threshold is `L < 8` and the problem advertises `7.99`. Second, **uniqueness is a rigidity
principle**: because the equation is invariant under the reflection `t \mapsto 1-t` (a symmetry of `f`
that respects the boundary conditions), its unique solution must be invariant too. One never solves for
`x`; one only observes that `x(1-t)` solves the same problem.

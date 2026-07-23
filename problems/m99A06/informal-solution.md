<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99A06: A convolution-quadratic equation solved by a small-parameter contraction in L¹

## Why It's Hard

The equation `f(x) + \sin x\int_{-\infty}^\infty f(x-y)f(y)\,dy = \epsilon e^{-x^2}` is **nonlinear** — the
unknown enters quadratically through a *convolution* `f * f` — so there is no closed form and no linear
solvability theory applies. Worse, the nonlinearity is nonlocal (a convolution) and is multiplied by the
unbounded-frequency factor `\sin x`, so naïve pointwise estimates are hopeless. One must find a function
space in which the quadratic term is *controlled by a norm*, set up a fixed-point map, and prove it
contracts.

The right space is not obvious. The crucial structural facts — that `L^1(\mathbb R)` is a **Banach algebra
under convolution** (`\|f*g\|_1 \le \|f\|_1\|g\|_1`, Young's inequality) and that multiplication by the
bounded function `\sin x` is a **contraction** on `L^1` (`|\sin| \le 1`) — are exactly what tame the
nonlinear term. Once those are in hand, the smallness of `\epsilon` makes the solution small, so the
quadratic term `\sim \|f\|_1^2` is subdominant to the linear forcing `\sim \epsilon`, and a contraction on a
small ball closes the argument.

## The Key Insight

Rewrite the equation as a fixed point:

$$f = T(f), \qquad (Tf)(x) = \epsilon e^{-x^2} - \sin x\,(f * f)(x).$$

In `L^1(\mathbb R)`, two inequalities govern `T`:

- **Convolution is sub-multiplicative:** `\|f*f\|_1 \le \|f\|_1^2` (Young).
- **`\sin x` is a contraction multiplier:** `\|\sin(\cdot)\,h\|_1 = \int |\sin x|\,|h(x)|\,dx \le \|h\|_1`.

Hence `\|Tf\|_1 \le \epsilon\sqrt\pi + \|f\|_1^2` and `\|Tf - Tg\|_1 \le (\|f\|_1 + \|g\|_1)\|f-g\|_1` (using
`\|e^{-x^2}\|_1 = \sqrt\pi`). On a ball of radius `r \sim \epsilon\sqrt\pi`, `T` is a self-map and a
contraction once `\epsilon` is small (the quadratic contribution `r^2 \sim \epsilon^2` is negligible against
the forcing `\epsilon`). Banach's theorem then yields a solution `f \in L^1`.

## Complete Proof

Work in the Banach space `X = L^1(\mathbb R)` with `\|\cdot\|_1`. Note `\|e^{-x^2}\|_1 = \int_{-\infty}^\infty e^{-x^2}\,dx = \sqrt\pi`.
Define

$$(Tf)(x) = \epsilon\, e^{-x^2} - \sin x\,(f * f)(x), \qquad (f*f)(x) = \int_{-\infty}^\infty f(x-y)f(y)\,dy.$$

A function `f \in L^1` solves the equation iff `Tf = f`.

**`T` maps `L^1` into `L^1`.** By Young's inequality `f*f \in L^1` with `\|f*f\|_1 \le \|f\|_1^2`, and
multiplication by the bounded `\sin x` keeps it in `L^1`. So `Tf \in L^1`, and

$$\|Tf\|_1 \le \epsilon\|e^{-x^2}\|_1 + \big\|\sin(\cdot)\,(f*f)\big\|_1
\le \epsilon\sqrt\pi + \|f*f\|_1 \le \epsilon\sqrt\pi + \|f\|_1^2. \tag{1}$$

**Contraction estimate.** Using `f*f - g*g = f*(f-g) + (f-g)*g` and Young's inequality,

$$\|f*f - g*g\|_1 \le \|f\|_1\|f-g\|_1 + \|f-g\|_1\|g\|_1 = (\|f\|_1 + \|g\|_1)\,\|f-g\|_1,$$

so, since `\|\sin(\cdot)\,h\|_1 \le \|h\|_1`,

$$\|Tf - Tg\|_1 = \big\|\sin(\cdot)\,(f*f - g*g)\big\|_1 \le (\|f\|_1 + \|g\|_1)\,\|f-g\|_1. \tag{2}$$

**Choice of ball.** Let `\delta = \epsilon\sqrt\pi`, fix the radius `r = 2\delta = 2\epsilon\sqrt\pi`, and let
`B_r = \{f \in L^1 : \|f\|_1 \le r\}`, a complete metric space (closed ball in the Banach space `L^1`). Assume

$$0 < \epsilon < \frac{1}{4\sqrt\pi}.$$

- *Self-map.* For `\|f\|_1 \le r`, by (1), `\|Tf\|_1 \le \delta + r^2 = \delta + 4\epsilon^2\pi`. This is
  `\le r = 2\delta` iff `4\epsilon^2\pi \le \delta = \epsilon\sqrt\pi`, i.e. `4\epsilon\sqrt\pi \le 1`, which
  holds. So `T(B_r) \subseteq B_r`.
- *Contraction.* For `f, g \in B_r`, `\|f\|_1 + \|g\|_1 \le 2r = 4\epsilon\sqrt\pi`, so by (2)
  `\|Tf - Tg\|_1 \le 4\epsilon\sqrt\pi\,\|f-g\|_1 = \kappa\,\|f-g\|_1` with `\kappa = 4\epsilon\sqrt\pi < 1`.

**Conclusion.** For `0 < \epsilon < \tfrac{1}{4\sqrt\pi}`, `T` is a contraction of the complete space `B_r`
into itself, so by the **Banach fixed-point theorem** it has a (unique) fixed point `f \in B_r \subseteq L^1`.
This `f` satisfies

$$\boxed{\ f(x) + \sin x \int_{-\infty}^\infty f(x-y)f(y)\,dy = \epsilon\, e^{-x^2}, \qquad f \in L^1(\mathbb R).\ }$$

In particular, at least one `L^1` solution exists for all sufficiently small `\epsilon > 0`. ∎

**Remark.** The solution is in fact *unique within the small ball* `B_{2\epsilon\sqrt\pi}` and satisfies
`\|f\|_1 \le 2\epsilon\sqrt\pi`, so `f \to 0` as `\epsilon \to 0` with leading behaviour `f \approx \epsilon e^{-x^2}`
(the convolution correction is `O(\epsilon^2)`). The argument is the same small-parameter contraction used for
nonlinear integral equations, but staged in `L^1` rather than `C`: the two facts that make it run are that
`L^1(\mathbb R)` is a **Banach algebra under convolution** (so the quadratic term is controlled by `\|f\|_1^2`)
and that the oscillatory coefficient `\sin x` is harmless because it is a bounded multiplier. The ball radius
is scaled to the forcing, `r \sim \epsilon`, which is what renders the quadratic nonlinearity a subdominant
perturbation.

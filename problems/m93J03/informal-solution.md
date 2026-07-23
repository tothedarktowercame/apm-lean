<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93J03: A nonlinear integral equation — finite-dimensional reduction and the implicit function theorem

## Why It's Hard

The instinct is Banach's fixed-point theorem: set `(Tx)(t) = ε + \int_{-\pi}^{\pi} \sin(t+s+x(s))\,ds`
on `C[-\pi,\pi]` and show `T` is a contraction. But it is **not**. Since `\sin` is
`1`-Lipschitz,

$$\|Tx - Ty\|_\infty \le \sup_t \int_{-\pi}^{\pi} |x(s)-y(s)|\,ds \le 2\pi\,\|x-y\|_\infty,$$

and this estimate is sharp in order: the Lipschitz constant is `2\pi \approx 6.28 > 1`.
No choice of ball helps, because the constant is uniform. The naive contraction is dead
on arrival, and that is the whole point of the problem — it is engineered to defeat the
reflex and force you to *use the structure of the kernel* rather than brute-force estimate
it.

The second difficulty is that there is no closed-form solution to exhibit; you must prove
existence and uniqueness abstractly while the equation is genuinely nonlinear in `x`.

## The Key Insight

The kernel `\sin(t+s+x(s))` separates in `t`. By the angle-addition formula,

$$\sin\big(t + (s + x(s))\big) = \sin t\,\cos(s+x(s)) + \cos t\,\sin(s+x(s)),$$

so the integral operator always outputs a function of the special form

$$(Tx)(t) = \epsilon + a\,\sin t + b\,\cos t,\qquad
a = \int_{-\pi}^{\pi}\cos(s+x(s))\,ds,\quad b = \int_{-\pi}^{\pi}\sin(s+x(s))\,ds.$$

**Every solution therefore lives in the three-parameter family `x(t) = ε + a\sin t + b\cos t`** —
an *exact* collapse of an infinite-dimensional problem onto two scalar unknowns `(a,b)`. The
problem becomes a `2\times2` system, and the rest is the implicit function theorem:

- at `ε = 0` the obvious candidate `x \equiv 0` is a genuine solution (a clean cancellation,
  `\int_{-\pi}^{\pi}\sin(t+s)\,ds = 0`), giving the base point `(a,b,ε)=(0,0,0)`;
- the Jacobian of the reduced system there is diagonal with determinant `1-\pi^2 \ne 0`,
  precisely *because* `\pi \ne 1` — the same factor `\pi` that made the naive contraction
  fail is what makes the reduction succeed.

## Complete Proof

Work in `X = C[-\pi,\pi]` with the sup norm, and define
`(Tx)(t) = \epsilon + \int_{-\pi}^{\pi}\sin(t+s+x(s))\,ds`. A continuous `x` solves the
equation iff `Tx = x`.

### Step 1 — Exact reduction to two unknowns

For any `x \in X`, expand the kernel by the addition formula:

$$(Tx)(t) = \epsilon + \sin t\int_{-\pi}^{\pi}\cos(s+x(s))\,ds
+ \cos t\int_{-\pi}^{\pi}\sin(s+x(s))\,ds = \epsilon + a\,\sin t + b\,\cos t,$$

where `a := \int_{-\pi}^{\pi}\cos(s+x(s))\,ds` and `b := \int_{-\pi}^{\pi}\sin(s+x(s))\,ds`.
Hence **the range of `T` consists entirely of functions `t \mapsto \epsilon + a\sin t + b\cos t`**.
Any fixed point `x = Tx` must itself have this form, so we may write

$$x(t) = \epsilon + a\sin t + b\cos t$$

and substitute it back into the formulas for `a, b`. With `\theta(s) := s + \epsilon + a\sin s + b\cos s`,
the equation `Tx = x` is **equivalent** to the `2\times2` system

$$a = F(a,b,\epsilon) := \int_{-\pi}^{\pi}\cos\theta(s)\,ds,\qquad
b = G(a,b,\epsilon) := \int_{-\pi}^{\pi}\sin\theta(s)\,ds. \tag{$\star$}$$

This equivalence is exact, not approximate: solving the integral equation in `C[-\pi,\pi]`
is the *same* as solving `(\star)` in `\mathbb{R}^2`.

### Step 2 — The base solution at `ε = 0`

Try `(a,b,\epsilon) = (0,0,0)`, i.e. `\theta(s) = s`:

$$F(0,0,0) = \int_{-\pi}^{\pi}\cos s\,ds = [\sin s]_{-\pi}^{\pi} = 0,\qquad
G(0,0,0) = \int_{-\pi}^{\pi}\sin s\,ds = 0.$$

So `(\star)` holds: `(a,b) = (0,0)` is a solution at `\epsilon = 0`, corresponding to
`x \equiv 0`. (Equivalently, directly, `\int_{-\pi}^{\pi}\sin(t+s)\,ds = [-\cos(t+s)]_{-\pi}^{\pi} = 0`.)

### Step 3 — The implicit function theorem

Define `H : \mathbb{R}^3 \to \mathbb{R}^2` by `H(a,b,\epsilon) = \big(a - F,\ b - G\big)`. The
integrands and all their partials are continuous and bounded on compact sets, so we may
differentiate under the integral sign; `H` is `C^1` (indeed `C^\infty`). By Step 2,
`H(0,0,0) = (0,0)`.

Compute the partial derivatives at the base point, where `\theta(s) = s`:

$$F_a = \int_{-\pi}^{\pi} -\sin\theta\,(\sin s)\,ds \Big|_{0}
= -\int_{-\pi}^{\pi}\sin^2 s\,ds = -\pi,\qquad
F_b = -\int_{-\pi}^{\pi}\sin s\cos s\,ds = 0,$$

$$G_a = \int_{-\pi}^{\pi}\cos\theta\,(\sin s)\,ds\Big|_0 = \int_{-\pi}^{\pi}\cos s\sin s\,ds = 0,\qquad
G_b = \int_{-\pi}^{\pi}\cos s\cos s\,ds = \pi.$$

Therefore the partial Jacobian of `H` in `(a,b)` at `(0,0,0)` is

$$D_{(a,b)}H(0,0,0) =
\begin{pmatrix} 1 - F_a & -F_b \\ -G_a & 1 - G_b \end{pmatrix}
= \begin{pmatrix} 1+\pi & 0 \\ 0 & 1-\pi \end{pmatrix},
\qquad \det = (1+\pi)(1-\pi) = 1 - \pi^2.$$

Since `\pi > 1`, `\det = 1 - \pi^2 \approx -8.87 \ne 0`, so `D_{(a,b)}H(0,0,0)` is invertible.

By the **implicit function theorem**, there exist `\delta > 0`, a neighborhood
`W \ni (0,0)` in `\mathbb{R}^2`, and a unique `C^1` map `\epsilon \mapsto (a(\epsilon), b(\epsilon))`
with `(a(0),b(0)) = (0,0)` such that, for every `\epsilon` with `|\epsilon| < \delta`,
`(a(\epsilon), b(\epsilon))` is the **unique** solution of `(\star)` lying in `W`.

### Step 4 — Conclusion

For `|\epsilon| < \delta`, set

$$x_\epsilon(t) = \epsilon + a(\epsilon)\sin t + b(\epsilon)\cos t.$$

By the exact equivalence of Step 1, `x_\epsilon` is a continuous solution of the integral
equation, and it is the unique solution with parameters `(a,b) \in W` — that is, the unique
continuous solution near the trivial solution `x \equiv 0` of the `\epsilon = 0` problem. As
`\epsilon \to 0`, `(a(\epsilon),b(\epsilon)) \to (0,0)`, so `x_\epsilon \to 0` uniformly,
and `x_\epsilon` depends continuously (indeed `C^1`) on `\epsilon`.

Thus for all `\epsilon \in \mathbb{R}` of sufficiently small magnitude there is a unique
continuous function `x` on `[-\pi,\pi]` satisfying
`x(t) = \epsilon + \int_{-\pi}^{\pi}\sin(t+s+x(s))\,ds`. ∎

**Remark.** The two `\pi`'s are the same `\pi` wearing two hats. The naive contraction
failed with constant `2\pi > 1`; the reduction succeeded because the Jacobian determinant
`1 - \pi^2` is nonzero. The lesson is that when a global contraction estimate is too lossy,
one should look for *structure in the kernel* — here a separation of variables that compresses
the problem to finitely many dimensions, where the implicit function theorem (a local
contraction in disguise, via the invertible linear part) finishes the job.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94A05: A quadratic integral equation solved by a small-parameter contraction

## Why It's Hard

The equation `u(t) + \int_0^\pi \sin(ts)\,u(s)^2\,ds = \epsilon\sin t` is **nonlinear** — the
unknown appears squared inside the integral — so there is no closed-form solution and no linear
solvability theory (Fredholm, Lax–Milgram) applies directly. The natural move is to rewrite it as
a fixed-point problem `u = Tu` and invoke Banach's contraction theorem, but here is the catch:
the quadratic map `u \mapsto u^2` is **not** a contraction on all of `C([0,\pi])`, nor even on any
fixed ball of radius `\ge 1/(2\pi)`. Its Lipschitz constant grows with the size of `u`, so a global
or large-ball contraction is impossible.

The resolution requires coordinating two things at once: the size of the forcing `\epsilon` and the
radius of the ball on which you work. You cannot fix the ball first; its radius must be chosen as a
function of `\epsilon` so that the quadratic term stays negligible. Seeing that the ball must
**shrink with `\epsilon`** is the crux.

## The Key Insight

Rearrange to `u(t) = \epsilon\sin t - \int_0^\pi \sin(ts)\,u(s)^2\,ds =: (Tu)(t)`, and look for a
fixed point in a ball `B_r = \{\|u\|_\infty \le r\}` whose radius `r` is **scaled to the forcing**,
`r \sim \epsilon`. Then:

- the linear forcing contributes `\epsilon` to `\|Tu\|`;
- the quadratic term contributes only `O(r^2) = O(\epsilon^2)`, which is *subdominant* to `\epsilon`
  once `\epsilon` is small;
- the contraction constant is `\pi(\|u\|+\|v\|) \le 2\pi r = O(\epsilon)`, automatically `<1` for
  small `\epsilon`.

So choosing `r = 2\epsilon` makes `T` both a self-map of `B_r` and a contraction the moment
`\epsilon \le 1/(4\pi)`. The quadratic nonlinearity, fatal on a large ball, is harmless on a ball
of radius `O(\epsilon)` because there the term it controls is one order smaller than the data.

## Complete Proof

Work in the Banach space `X = C([0,\pi])` with `\|\cdot\|_\infty`. Define `T: X \to X` by

$$(Tu)(t) = \epsilon\sin t - \int_0^\pi \sin(ts)\,u(s)^2\,ds.$$

`Tu` is continuous in `t` (the integrand is continuous in `t` and dominated by the integrable
`u(s)^2`), so `T` indeed maps `X` into `X`, and `u` solves the integral equation iff `u = Tu`.

**Estimate 1 — size of `Tu`.** Since `|\sin(ts)| \le 1`,

$$\|Tu\|_\infty \le \epsilon\,\|\sin\|_\infty + \sup_t \int_0^\pi |\sin(ts)|\,u(s)^2\,ds
\le \epsilon + \int_0^\pi u(s)^2\,ds \le \epsilon + \pi\,\|u\|_\infty^2. \tag{1}$$

**Estimate 2 — contraction.** For `u,v \in X`, using `u^2 - v^2 = (u+v)(u-v)`,

$$|(Tu)(t) - (Tv)(t)| = \Big|\int_0^\pi \sin(ts)\,(u(s)+v(s))(u(s)-v(s))\,ds\Big|
\le \|u-v\|_\infty \int_0^\pi |u+v|\,ds,$$

so

$$\|Tu - Tv\|_\infty \le \pi\big(\|u\|_\infty + \|v\|_\infty\big)\,\|u-v\|_\infty. \tag{2}$$

**Choice of ball.** Fix `r = 2\epsilon` and let `B_r = \{u \in X : \|u\|_\infty \le r\}`, a closed
(hence complete) subset of `X`. Assume `0 < \epsilon \le \tfrac{1}{4\pi}`.

*`T` maps `B_r` into `B_r`:* for `\|u\|_\infty \le r = 2\epsilon`, by (1),

$$\|Tu\|_\infty \le \epsilon + \pi (2\epsilon)^2 = \epsilon(1 + 4\pi\epsilon) \le \epsilon\cdot 2 = 2\epsilon = r,$$

where `4\pi\epsilon \le 1` was used. So `Tu \in B_r`.

*`T` is a contraction on `B_r`:* for `u,v \in B_r`, `\|u\|_\infty + \|v\|_\infty \le 2r = 4\epsilon`,
so by (2),

$$\|Tu - Tv\|_\infty \le \pi\cdot 4\epsilon\,\|u-v\|_\infty = 4\pi\epsilon\,\|u-v\|_\infty
= \kappa\,\|u-v\|_\infty,\qquad \kappa = 4\pi\epsilon.$$

For `0 < \epsilon < \tfrac{1}{4\pi}` we have `\kappa < 1`, a strict contraction.

**Conclusion.** For `0 < \epsilon < \tfrac{1}{4\pi}`, `T` is a contraction of the complete metric
space `B_r` into itself, so by the **Banach fixed-point theorem** it has a unique fixed point
`u \in B_r`. This `u \in C([0,\pi])` satisfies

$$u(t) + \int_0^\pi \sin(ts)\,u(s)^2\,ds = \epsilon\sin t,$$

which is the desired solution. ∎

**Remarks.** (i) The solution is *unique within the ball* `B_{2\epsilon}` and satisfies
`\|u\|_\infty \le 2\epsilon`, so `u \to 0` as `\epsilon \to 0`. (ii) To leading order `u(t) \approx \epsilon\sin t`,
since the quadratic correction `\int_0^\pi \sin(ts)u(s)^2 ds = O(\epsilon^2)` is one order smaller —
exactly the heuristic that the small-parameter contraction makes rigorous. (iii) The threshold
`1/(4\pi)` is an artifact of the crude bounds `|\sin| \le 1` and the choice `r = 2\epsilon`; any
`r = c\,\epsilon` with `c > 1` works for `\epsilon` small enough, so the precise constant is not
important — only that such a coordinated choice exists.

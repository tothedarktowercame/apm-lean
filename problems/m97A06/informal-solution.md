<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m97A06: A pendulum-type variational problem — Euler–Lagrange, energy, and a positive-definite Hessian

## Why It's Hard

This is a guided tour through the calculus of variations for the Lagrangian
`L(\varphi,\varphi') = \tfrac12\varphi'^2 - \tfrac14\cos(2\varphi)`, and each part exercises a different
piece of machinery. The Euler–Lagrange equation is a straightforward computation, but the conceptual
content is recognizing the *structure*: (b) is a conservation law that follows from the Lagrangian having
no explicit time dependence (Noether/Beltrami), and proving it requires using the Euler–Lagrange equation
itself, not just differentiating blindly. Part (d), the second variation, is the genuinely subtle one — it
is the Hessian of the *functional* on an infinite-dimensional space of variations, and one must compute it
as a quadratic form and decide its definiteness.

The deepest point is a sign that is easy to get backwards. The equilibrium `\varphi \equiv 0` is a
**maximum** of the mechanical potential `V(\varphi) = \tfrac14\cos(2\varphi)` (an *unstable* equilibrium of
the pendulum), yet it is a **strict local minimizer** of the action `I`. The two notions of "stability"
genuinely differ, because the second-variation operator is `-d^2/dt^2 + 1`, which is positive definite —
so there is no contradiction, only a reminder that mechanical instability and being an action-minimizer are
controlled by *opposite* signs of `V''`.

## The Key Insight

- **(a)** `\partial_{\varphi'}L = \varphi'`, `\partial_\varphi L = \tfrac12\sin(2\varphi)`, so Euler–Lagrange
  is `\varphi'' = \tfrac12\sin(2\varphi)` — the (inverted) pendulum equation.
- **(b)** Because `L` has no explicit `t`, the energy `E = \varphi'\partial_{\varphi'}L - L = \tfrac12\varphi'^2 + \tfrac14\cos(2\varphi)`
  is conserved; differentiating it gives `\varphi'(\varphi'' - \tfrac12\sin 2\varphi) = 0`, which vanishes
  by Euler–Lagrange.
- **(c)** `\varphi \equiv 0` solves `\varphi'' = \tfrac12\sin(2\varphi)` (both sides `0`) with `\varphi(0)=\varphi(T)=0`.
- **(d)** The second variation at `\varphi \equiv 0` is `\delta^2 I[h] = \int_0^T (h'^2 + h^2)\,dt > 0` — its
  Jacobi operator `-d^2/dt^2 + 1` has eigenvalues `1 + (n\pi/T)^2 > 0`, so the Hessian is positive definite
  and `\varphi \equiv 0` is a strict local minimum.

## Complete Proof

Write `L(\varphi,\varphi') = \tfrac12\varphi'^2 - \tfrac14\cos(2\varphi)`, so
`I(\varphi) = \int_0^T L\,dt` over `C^1` functions with `\varphi(0)=\alpha`, `\varphi(T)=\beta`.

### (a) Euler–Lagrange equation

Compute the partials:

$$\frac{\partial L}{\partial \varphi'} = \varphi', \qquad
\frac{\partial L}{\partial \varphi} = -\frac14\cdot(-2\sin(2\varphi)) = \frac12\sin(2\varphi).$$

The Euler–Lagrange equation `\dfrac{d}{dt}\dfrac{\partial L}{\partial\varphi'} - \dfrac{\partial L}{\partial\varphi} = 0` is

$$\boxed{\ \varphi''(t) = \tfrac12\sin\big(2\varphi(t)\big).\ }$$

### (b) Conservation of `\tfrac12\varphi'^2 + \tfrac14\cos(2\varphi)`

Differentiate the claimed quantity along any solution and use part (a):

$$\frac{d}{dt}\Big[\frac12\varphi'^2 + \frac14\cos(2\varphi)\Big]
= \varphi'\varphi'' + \frac14(-\sin 2\varphi)\cdot 2\varphi'
= \varphi'\Big(\varphi'' - \frac12\sin 2\varphi\Big) = \varphi'\cdot 0 = 0.$$

Hence `\tfrac12\varphi'^2 + \tfrac14\cos(2\varphi)` is **constant** on every solution. (Structurally this is
the conserved energy `E = \varphi'\,\partial_{\varphi'}L - L`, conserved because `L` does not depend
explicitly on `t`.) ∎

### (c) A solution with `\varphi(0) = \varphi(T) = 0`

Try the constant `\varphi \equiv 0`. Then `\varphi'' = 0` and `\tfrac12\sin(2\cdot 0) = 0`, so the
Euler–Lagrange equation `\varphi'' = \tfrac12\sin 2\varphi` holds, and the boundary conditions
`\varphi(0) = \varphi(T) = 0` are satisfied. Therefore

$$\boxed{\ \varphi \equiv 0\ }$$

is a solution. ∎

### (d) The second variation (Hessian) at `\varphi \equiv 0`

For a variation `h \in C^1[0,T]` with `h(0) = h(T) = 0`, the second variation is

$$\delta^2 I(\varphi)[h] = \int_0^T \Big[L_{\varphi'\varphi'}\,h'^2 + 2L_{\varphi\varphi'}\,h h' + L_{\varphi\varphi}\,h^2\Big]\,dt.$$

The second derivatives of `L` are

$$L_{\varphi'\varphi'} = 1, \qquad L_{\varphi\varphi'} = 0, \qquad
L_{\varphi\varphi} = \frac{\partial}{\partial\varphi}\Big(\frac12\sin 2\varphi\Big) = \cos(2\varphi).$$

Evaluating at the solution `\varphi \equiv 0` (`\cos 0 = 1`),

$$\boxed{\ \delta^2 I(0)[h] = \int_0^T \big(h'(t)^2 + h(t)^2\big)\,dt.\ }$$

This quadratic form is **positive definite**: `\delta^2 I(0)[h] > 0` for every `h \not\equiv 0`. Integrating
by parts (`h(0)=h(T)=0`), `\delta^2 I(0)[h] = \int_0^T \big[(-h'' + h)h\big]\,dt`, so the associated **Jacobi
operator** is `-\dfrac{d^2}{dt^2} + 1` with Dirichlet boundary conditions, whose eigenvalues are
`1 + (n\pi/T)^2 > 0` (`n = 1, 2, \dots`). All positive, so the Hessian is positive definite and
`\varphi \equiv 0` is a **strict local minimum** of `I`. ∎

**Remark.** The potential `V(\varphi) = \tfrac14\cos(2\varphi)` has `V''(0) = -1 < 0`, so `\varphi = 0` is a
*maximum* of `V` — an unstable equilibrium of the underlying pendulum. Yet it is a strict *minimizer* of the
action, because the second variation's mass term is `L_{\varphi\varphi}(0) = -V''(0) = +1 > 0`, making the
Jacobi operator `-d^2/dt^2 + 1` positive with no conjugate points on `[0,T]`. The sign flips between
"mechanically stable equilibrium" (`V'' > 0`) and "action-minimizing trajectory" (`-V'' > 0`); they are not
the same condition, and this problem is the clean illustration of the difference.

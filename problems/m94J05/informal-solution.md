<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94J05: A nonlinear Euler-equation BVP — invert the linear part, then contract

## Why It's Hard

The boundary value problem `t^2 x'' + 2t x' = f(t) + x(t)^2`, `x(1)=x(2)=0`, is **nonlinear**: the
term `x^2` destroys superposition, so none of the linear BVP machinery (Green's functions,
eigenfunction expansions) applies *directly*. There is no formula for the solution, and one must
prove existence and uniqueness abstractly while controlling a quadratic nonlinearity.

The structural difficulty is to find the right fixed-point formulation. A naive Picard iteration on
the second-order ODE is awkward because of the boundary conditions at *both* endpoints — an initial
value reformulation does not respect `x(2)=0`. The hint points to the resolution: peel off the linear
operator `Lx := t^2 x'' + 2t x'`, **invert it once and for all** (it is the Green's operator for the
two-point problem, and it automatically builds in the boundary conditions), and recast the BVP as the
fixed-point equation `x = L^{-1}(f + x^2)`. The remaining work is to show this map contracts — which it
does precisely when `\max|f|` is small, because then the solution is small and the quadratic term is a
subdominant perturbation.

## The Key Insight

`Lx = t^2 x'' + 2t x' = (t^2 x')'` is an **exact derivative** — an Euler (equidimensional) operator in
divergence form. The homogeneous Dirichlet problem `(t^2 x')' = 0`, `x(1)=x(2)=0` has only the trivial
solution, so `L` is invertible on `\{x \in C^2[1,2] : x(1)=x(2)=0\}`, with a bounded Green's operator
`L^{-1} : C[1,2] \to C[1,2]` (norm `M < \infty`) that **maps any continuous right-hand side to a `C^2`
function already satisfying the boundary conditions.** Writing `Lx = F(x) := f + x^2` as `x = T(x) := L^{-1}f + L^{-1}(x^2)`,
the two estimates

$$\|T(x)\| \le M\|f\| + M\|x\|^2, \qquad \|T(x) - T(y)\| \le M\big(\|x\| + \|y\|\big)\|x - y\|$$

show that on a ball of radius `r \sim M\|f\|`, `T` is a self-map and a contraction once `\|f\|` is small:
the quadratic term contributes `O(r^2)`, negligible against the linear forcing `O(r)`. Banach's theorem
then delivers a unique small solution. The smallness of `f` is exactly what keeps the nonlinearity weak.

## Complete Proof

Work in `X = C[1,2]` with the sup norm `\|\cdot\|`, and let `Lx = t^2 x'' + 2t x'`.

**Step 1 — `L` in divergence form and its invertibility.** Observe `\dfrac{d}{dt}(t^2 x') = 2t x' + t^2 x''`,
so

$$Lx = (t^2 x')'.$$

The homogeneous equation `(t^2 x')' = 0` gives `t^2 x' = c_1`, hence `x = -c_1/t + c_2`, a two-dimensional
space spanned by `1` and `1/t`. Imposing `x(1) = x(2) = 0`:

$$-c_1 + c_2 = 0,\qquad -\tfrac{c_1}{2} + c_2 = 0 \ \Longrightarrow\ c_1 = c_2 = 0.$$

So the homogeneous Dirichlet problem has **only** the trivial solution, and `L` is invertible on
`D = \{x \in C^2[1,2] : x(1)=x(2)=0\}`.

**Step 2 — The bounded Green's operator `L^{-1}`.** Take the homogeneous solutions adapted to the
endpoints, `\varphi_1(t) = 1 - \tfrac1t` (so `\varphi_1(1)=0`) and `\varphi_2(t) = 1 - \tfrac2t` (so
`\varphi_2(2)=0`). Their Wronskian-flux is constant:

$$t^2\big(\varphi_1 \varphi_2' - \varphi_1'\varphi_2\big)
= t^2\cdot \frac{1}{t^2} = 1 \ne 0,$$

(using `\varphi_1' = 1/t^2`, `\varphi_2' = 2/t^2`), confirming independence. Hence the two-point problem
`Lx = g`, `x(1)=x(2)=0` has the Green's-function solution

$$x(t) = (L^{-1}g)(t) = \int_1^2 G(t,s)\,g(s)\,ds, \qquad
G(t,s) = \begin{cases}\varphi_1(s)\,\varphi_2(t), & 1\le s \le t,\\[2pt] \varphi_1(t)\,\varphi_2(s), & t \le s \le 2,\end{cases}$$

with `G` continuous on `[1,2]^2` (the flux normalization is `1`). Since `\varphi_1, \varphi_2` are bounded
on `[1,2]`, `G` is bounded, so `L^{-1} : C[1,2] \to C[1,2]` is a bounded linear operator with

$$M := \|L^{-1}\| = \sup_{t\in[1,2]} \int_1^2 |G(t,s)|\,ds < \infty.$$

Crucially, for continuous `g`, `L^{-1}g \in C^2[1,2]` and satisfies the boundary conditions.

**Step 3 — Fixed-point reformulation.** A function `x \in D` solves the BVP iff `Lx = f + x^2`, i.e. iff

$$x = T(x), \qquad T(x) := L^{-1}\big(f + x^2\big) = L^{-1}f + L^{-1}(x^2).$$

Because `L^{-1}` lands in `D`, any fixed point of `T` automatically lies in `C^2[1,2]` with `x(1)=x(2)=0`,
and solves the differential equation.

**Step 4 — `T` is a contraction on a small ball.** For `x, y \in X`, using linearity and boundedness of
`L^{-1}` and `\|x^2\| = \|x\|^2`, `\|x^2 - y^2\| = \|(x+y)(x-y)\| \le (\|x\|+\|y\|)\|x-y\|`:

$$\|T(x)\| \le M\|f\| + M\|x\|^2, \qquad \|T(x) - T(y)\| \le M\big(\|x\|+\|y\|\big)\,\|x-y\|. \tag{$\ast$}$$

Let `\delta = \|f\| = \max_{[1,2]}|f|`. Fix the radius `r = 2M\delta` and the closed ball
`B_r = \{x \in X : \|x\| \le r\}` (complete). Assume `\delta < \dfrac{1}{4M^2}`.

- *Self-map:* for `\|x\| \le r`, by `(\ast)`, `\|T(x)\| \le M\delta + M(2M\delta)^2 = M\delta(1 + 4M^2\delta) \le M\delta\cdot 2 = 2M\delta = r`,
  using `4M^2\delta \le 1`. So `T(B_r) \subseteq B_r`.
- *Contraction:* for `x,y \in B_r`, `\|x\|+\|y\| \le 2r = 4M\delta`, so by `(\ast)`,
  `\|T(x)-T(y)\| \le M\cdot 4M\delta\,\|x-y\| = 4M^2\delta\,\|x-y\|`, with `\kappa := 4M^2\delta < 1`.

**Step 5 — Conclusion.** By the **Banach fixed-point theorem**, `T` has a unique fixed point `x \in B_r`.
By Step 3, `x \in C^2[1,2]`, `x(1)=x(2)=0`, and `t^2 x'' + 2t x' = f + x^2` on `[1,2]`. Thus for
`\max|f| < \tfrac{1}{4M^2}` there is a unique such (small) solution. ∎

**Remark (sense of uniqueness).** The contraction gives uniqueness within `B_r`; this is the natural
reading, since the quadratic equation may admit large solutions unrelated to the data. Uniqueness among
small solutions can also be seen directly: if `x, y` both solve the BVP, then `w = x - y` satisfies
`(t^2 w')' = (x+y)w`, `w(1)=w(2)=0`; multiplying by `w` and integrating by parts,

$$\int_1^2 t^2 (w')^2\,dt = -\int_1^2 (x+y)\,w^2\,dt \le 2r\int_1^2 w^2\,dt.$$

With `t^2 \ge 1` and the Poincaré (Wirtinger) inequality `\int_1^2 (w')^2 \ge \pi^2 \int_1^2 w^2` on the
unit-length interval with zero endpoints, the left side is `\ge \pi^2\int w^2`, so
`(\pi^2 - 2r)\int w^2 \le 0`. For `r < \pi^2/2` this forces `w \equiv 0`, i.e. `x = y`. ∎

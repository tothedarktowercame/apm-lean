<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93J06: Picard–Lindelöf existence/uniqueness and the regularity of the flow map

## Why It's Hard

This is really five linked theorems of ODE theory, and the difficulty is that each part
requires a *different* tool while all resting on the same integral-equation reformulation.
Part (a) is the foundational existence/uniqueness theorem (Banach fixed point on the Picard
operator). Parts (b)–(e) are the genuinely subtle "dependence on data" statements: how does
the solution `y(t;y_0)` inherit regularity — `C^1`, Hölder, global-in-time — from the
right-hand side `f`?

The trap in (d) is the most important conceptual point in the whole problem. One is tempted
to read "`f` Hölder-`α`" as "Hölder in `y`," but **Hölder-in-`y` (with `α<1`) is not enough
even for uniqueness** — `y' = |y|^{1/2}` famously has infinitely many solutions through
`y(0)=0`, and nearby initial data fan out by an `O(1)` amount no matter how close they start.
So the flow map cannot be made well-defined, let alone Hölder, under that hypothesis. The
hypothesis that makes the flow a bona fide function is **Lipschitz-in-`y`**; the Hölder
exponent `α` is then the modulus carried by the *time* variable, and it transfers to the
regularity of solutions and is preserved (with growing constants) by the flow. Recognizing
which modulus lives on which variable is the crux.

## The Key Insight

Everything runs through the **integral reformulation**

$$y' = f(x,y),\ y(0)=y_0 \iff y(x) = y_0 + \int_0^x f(s,y(s))\,ds,$$

and through **two integral inequalities** that convert pointwise bounds on `f` into global
bounds on solutions:

- **Grönwall (linear):** `u(t) \le C + \int_0^t \beta(s)u(s)\,ds \Rightarrow u(t) \le C\,e^{\int_0^t\beta}`.
  This single lemma proves uniqueness (a), continuous/Lipschitz dependence on `y_0` (d), and
  global existence under linear growth (c).
- **Bihari (nonlinear):** the `α`-Hölder analogue, which exposes exactly where uniqueness
  and continuous dependence can fail.

The differentiable dependence (b) is the **uniform contraction principle**: the Picard
operator is a contraction depending `C^1` on the parameter `y_0`, so its fixed point depends
`C^1` on `y_0`, and the derivative solves the *variational equation*. Finally (e) is the
**cocycle/group property** `\varphi_{t+s} = \varphi_t \circ \varphi_s`: local regularity plus
global existence (c) propagates the local results to all `t`, the only cost being constants
that grow like `e^{Ct}`.

## Complete Proof

### (a) Existence and uniqueness (Picard–Lindelöf)

**Theorem.** Let `f` be continuous on the rectangle `R = \{|x|\le a,\ |y-y_0|\le b\}` and
Lipschitz in `y`: `|f(x,y_1)-f(x,y_2)| \le L|y_1-y_2|` on `R`. Put `M = \max_R|f|` and
`h = \min(a, b/M)`. Then `y'=f(x,y),\ y(0)=y_0` has a unique `C^1` solution on `[-h,h]`.

**Proof.** A continuous `y` solves the Cauchy problem iff it solves the integral equation
`y = Ty`, where `(Ty)(x) = y_0 + \int_0^x f(s,y(s))\,ds`. Work in the complete metric space
`B = \{y \in C([-h,h]) : \|y-y_0\|_\infty \le b\}` (a closed ball in a Banach space).

*`T` maps `B` to `B`:* for `y\in B`, `|(Ty)(x)-y_0| = \big|\int_0^x f(s,y(s))ds\big| \le M|x| \le Mh \le b`.

*Some iterate of `T` is a contraction:* for `y,z\in B`, by induction

$$|(T^n y)(x) - (T^n z)(x)| \le \frac{(L|x|)^n}{n!}\,\|y-z\|_\infty \le \frac{(Lh)^n}{n!}\,\|y-z\|_\infty.$$

(Base `n=1`: `|Ty-Tz| \le L\int_0^{|x|}|y-z| \le L|x|\,\|y-z\|`. Inductive step integrates the
previous bound.) Since `(Lh)^n/n! \to 0`, `T^n` is a contraction for large `n`. By the Banach
fixed-point theorem (a map with a contracting iterate has a unique fixed point), `T` has a
unique fixed point `y \in B`. Being a fixed point of the integral equation with `f` continuous,
`y` is `C^1` and solves the Cauchy problem.

*Uniqueness* (global on the interval, via Grönwall): if `y,z` both solve it, then
`u(x):=|y(x)-z(x)|` satisfies `u(x) \le \int_0^{|x|} L\,u(s)\,ds`. Grönwall with `C=0` gives
`u\equiv 0`. ∎

---

### (b) `f \in C^1 \Rightarrow y_0 \mapsto y(t)` is `C^1` for small `t`

Since `f\in C^1`, `\partial_y f` is continuous, hence locally bounded, so `f` is locally
Lipschitz in `y` and (a) applies on a fixed interval `[-h,h]`. Let `X = C([-h,h])` and define
`F : \mathbb{R}\times X \to X` by

$$F(y_0, y) = y - \Big(y_0 + \int_0^{\,\cdot} f(s,y(s))\,ds\Big).$$

`F(y_0,y)=0` exactly when `y` is the solution with initial value `y_0`. The superposition
(Nemytskii) operator `y \mapsto f(\cdot,y(\cdot))` is `C^1` from `X` to `X` because `f\in C^1`,
with derivative `k \mapsto \partial_y f(\cdot,y(\cdot))\,k`; hence `F` is `C^1`. Its partial
derivative in `y` is `D_y F = I - K`, where `(K k)(x) = \int_0^x \partial_y f(s,y(s))k(s)\,ds`
has operator norm `\le \|\partial_y f\|_\infty\, h < 1` for `h` small. So `D_y F` is invertible.

By the **implicit function theorem in Banach space**, the solution `y_0 \mapsto y(\cdot\,;y_0)`
is a `C^1` map `\mathbb{R}\to X`. Composing with the bounded linear evaluation `y\mapsto y(t)`
shows `y_0 \mapsto y(t;y_0)` is `C^1` for `|t|\le h` ("sufficiently small `t`").

Differentiating the fixed-point relation in `y_0` shows `w(t) := \partial_{y_0} y(t;y_0)`
solves the **variational equation**

$$w'(t) = \partial_y f(t,y(t))\,w(t),\quad w(0)=1,\qquad\text{so}\quad
w(t) = \exp\!\Big(\int_0^t \partial_y f(s,y(s))\,ds\Big) > 0. \qquad\blacksquare$$

---

### (c) `|f(x,y)| \le C|y| \Rightarrow` the solution exists for all `t`

Local existence (a) gives a solution on a maximal interval `(T_-,T_+)`. On it, the integral
form gives `|y(t)| \le |y_0| + \int_0^{|t|} C|y(s)|\,ds`, so by **Grönwall**

$$|y(t)| \le |y_0|\,e^{C|t|}.$$

Thus on any *finite* interval the solution stays in a bounded (hence compact, after also
bounding `|y'| = |f| \le C|y|`) set. The **continuation theorem** says that if `T_+ < \infty`
the solution must leave every compact set as `t\to T_+^-` (it "blows up"). But `|y(t)|\le|y_0|e^{CT_+}`
stays bounded — contradiction. Hence `T_+ = +\infty`, and symmetrically `T_- = -\infty`. The
solution exists for all `t`. ∎

---

### (d) Hölder/Lipschitz dependence on `y_0` for small `t`

Keep the well-posedness hypothesis that `f` is **Lipschitz in `y`** (constant `L`), which is
what makes `y_0 \mapsto y(t)` a single-valued map at all (parts a, b). Fix `t` with `|t|\le h`
and two data `a,b`. Subtracting integral equations,

$$y(t;a) - y(t;b) = (a-b) + \int_0^t \big[f(s,y(s;a)) - f(s,y(s;b))\big]\,ds,$$

so `u(t):=|y(t;a)-y(t;b)|` obeys `u(t) \le |a-b| + L\int_0^{|t|} u(s)\,ds`. By **Grönwall**,

$$\boxed{\ |y(t;a) - y(t;b)| \le e^{L|t|}\,|a-b|.\ }$$

The map `y_0\mapsto y(t)` is therefore **Lipschitz** in `y_0`, with constant `e^{L|t|}\approx 1`
for small `t` — in particular Hölder of every exponent `\alpha\in(0,1]`. This is the modulus
of continuity the data-to-solution map inherits.

**What the Hölder exponent really controls.** If `f` is Hölder-`α` *in the time variable `x`*
(`|f(x,y)-f(x',y)|\le H|x-x'|^\alpha`), then since `y` is Lipschitz in `x` (because `|y'|=|f|`
is bounded), the composition `x\mapsto f(x,y(x))` is Hölder-`α`; hence `y' \in C^{0,\alpha}`,
i.e. each solution is `C^{1,\alpha}` in `t`. So the exponent `α` passes to the *time*
regularity of `y(t)`, while the dependence on `y_0` is Lipschitz by the boxed estimate.

**Why not Hölder-in-`y`.** If instead `f` were only Hölder-`α` *in `y`*
(`|f(x,y_1)-f(x,y_2)|\le K|y_1-y_2|^\alpha`, `α<1`), the same subtraction gives the *nonlinear*
inequality `u(t) \le |a-b| + K\int_0^{|t|} u(s)^\alpha ds`, and **Bihari's inequality** yields
only

$$u(t) \le \Big(|a-b|^{1-\alpha} + K(1-\alpha)|t|\Big)^{1/(1-\alpha)}.$$

For fixed `t>0` this does **not** tend to `0` as `|a-b|\to0` — it approaches
`(K(1-\alpha)|t|)^{1/(1-\alpha)} > 0`. That is exactly the fan-out of `y'=|y|^{1/2}`: Hölder-in-`y`
loses both uniqueness and continuous dependence. This is why Lipschitz-in-`y` is the right
hypothesis, and the boxed Grönwall estimate is the correct sense of part (d). ∎

---

### (e) Removing "small `t`" when `|f(x,y)| \le C|y|`

Under the linear-growth bound, part (c) gives a solution for **all** `t`, so the flow
`\varphi_t : y_0 \mapsto y(t;y_0)` is defined globally and satisfies the **cocycle property**
`\varphi_{t+s} = \varphi_t \circ \varphi_s` (by uniqueness, evolving by `s` then `t` equals
evolving by `t+s`). Any time `t` can be written as a finite composition of small-time steps
`\varphi_{h}\circ\cdots\circ\varphi_{h}`, each of which is `C^1` (part b) / Lipschitz (part d).

- **(b) globally:** a finite composition of `C^1` maps is `C^1`, so `y_0\mapsto y(t)` is `C^1`
  for *every* `t`, not just small `t`. By the chain rule its derivative is the product of the
  one-step variational factors, i.e. `w(t)=\exp(\int_0^t \partial_y f(s,y(s))\,ds)`.
- **(d) globally:** composing the per-step Grönwall bounds gives
  `|y(t;a)-y(t;b)| \le e^{L|t|}|a-b|` for all `t` — Lipschitz (hence Hölder-`α`) dependence on
  `y_0` on every finite interval.

So the *only* role of "sufficiently small `t`" in (b) and (d) was the local contraction window;
the linear-growth bound `|f|\le C|y|` removes it. The price is that the regularity constants
grow with `t` — like `e^{L|t|}` for the Lipschitz constant of the flow and
`\exp(\int_0^t \partial_y f)` for its derivative — but they remain finite for every finite `t`,
so the `C^1` and Lipschitz/Hölder dependence are **global in time**. ∎

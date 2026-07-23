<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98A03: Fréchet derivative of a Hammerstein integral operator on C[0,1], and continuity of u ↦ DF(u)

## Why It's Hard

The operator `F(u)(x) = ∫₀¹ K(x,y) f(u(y))\,dy` is nonlinear (through `f`) and infinite-dimensional, so
"differentiate it" means producing a *bounded linear operator* `DF(u₀)` on `C[0,1]` and verifying the
limit definition — not computing a number. Three things make this more than formal:

- **The derivative is an integral operator, found by differentiating *under the integral* and *inside*
  `f`.** The natural guess `[DF(u₀)h](x) = ∫₀¹ K(x,y) f'(u₀(y)) h(y)\,dy` has to be confirmed against the
  definition; guessing is not proving.
- **The remainder estimate needs uniformity, and that uniformity comes from compactness.** Pointwise
  Taylor expansion gives `f(u₀+h) − f(u₀) − f'(u₀)h = [f'(ξ_y) − f'(u₀(y))]h(y)`, but to make this
  `o(‖h‖)` in the *sup* norm you must bound `|f'(ξ_y) − f'(u₀(y))|` **uniformly in `y`**. The lever is that
  `u₀([0,1])` is compact, so `f'` is *uniformly* continuous on a compact neighborhood — only `C¹` of `f`
  plus compactness, nothing stronger.
- **Part (c) is the same uniform-continuity idea one level up:** continuity of `u ↦ DF(u)` reduces to an
  operator-norm bound `‖DF(u) − DF(u₀)‖ ≤ M_K · sup_y |f'(u(y)) − f'(u₀(y))|`, again controlled by uniform
  continuity of `f'` on a compact set. The subtlety is recognizing the operator norm collapses to a sup
  over `y` of the kernel difference.

## The Key Insight

Linearize *inside* the nonlinearity: replace `f(u₀(y)+h(y))` by its first-order Taylor term
`f(u₀(y)) + f'(u₀(y))h(y)`. This makes the derivative the **integral operator with kernel
`K(x,y) f'(u₀(y))`**:
$$[DF(u_0)h](x) = \int_0^1 K(x,y)\, f'(u_0(y))\, h(y)\,dy.$$
Both the remainder estimate (b) and the continuity of `u ↦ DF(u)` (c) then rest on one fact: because
`u₀([0,1])` (resp. `u([0,1])`) is **compact** and `f'` is continuous, `f'` is *uniformly* continuous
there, so its **modulus of continuity** `ω` controls everything:
$$\|F(u_0+h) - F(u_0) - DF(u_0)h\|_\infty \le M_K\,\omega(\|h\|_\infty)\,\|h\|_\infty = o(\|h\|),$$
$$\|DF(u) - DF(u_0)\|_{\mathrm{op}} \le M_K\,\omega(\|u-u_0\|_\infty) \to 0,$$
where `M_K = \max|K|`. The compactness-plus-`C¹` package is the whole engine.

## Complete Proof

### (a) Definition of Fréchet differentiability

Let `X, Y` be Banach spaces, `U ⊆ X` open, `F : U → Y`, and `x ∈ U`. We say `F` is **Fréchet
differentiable at `x`** if there exists a *bounded linear* operator `A ∈ \mathcal L(X,Y)` such that

$$
\lim_{\|h\|_X \to 0} \frac{\big\|F(x+h) - F(x) - A h\big\|_Y}{\|h\|_X} = 0 ,
$$

equivalently `F(x+h) = F(x) + A h + o(\|h\|_X)` as `h \to 0` (with `x+h ∈ U`). The operator `A`, when it
exists, is unique and is denoted `DF(x)`.

### (b) The Fréchet derivative of the Hammerstein operator

Here `X = Y = C([0,1])` with the sup norm `‖·‖ = ‖·‖_∞`, `K : [0,1]² → ℝ` continuous, `f ∈ C¹(ℝ)`. Write
`M_K = \max_{[0,1]^2}|K| < ∞`. (Each `F(u)` indeed lies in `C[0,1]`: `K` is uniformly continuous on the
compact square, so `x ↦ ∫_0^1 K(x,y)f(u(y))\,dy` is continuous.)

**Claim.** `F` is Fréchet differentiable at every `u₀ ∈ X`, with derivative the integral operator

$$
[DF(u_0)h](x) = \int_0^1 K(x,y)\, f'(u_0(y))\, h(y)\,dy , \qquad h \in X. \tag{$\ast$}
$$

**`A := DF(u_0)` is bounded and linear.** Linearity in `h` is clear. Let `J = u_0([0,1])`, a compact
subset of `ℝ` (continuous image of `[0,1]`); put `M' = \max_{s \in J}|f'(s)| < ∞` (continuity of `f'` on
compact `J`). Then for all `x`,
$$
|[Ah](x)| \le \int_0^1 |K(x,y)|\,|f'(u_0(y))|\,|h(y)|\,dy \le M_K\,M'\,\|h\|_\infty,
$$
and `Ah` is continuous in `x` (same uniform-continuity-of-`K` argument as for `F(u)`). Hence
`A ∈ \mathcal L(X,X)` with `‖A‖ ≤ M_K M'`.

**The remainder is `o(‖h‖)`.** Fix `‖h‖_∞ ≤ 1` and set
$$
R(x) := F(u_0+h)(x) - F(u_0)(x) - [Ah](x) = \int_0^1 K(x,y)\,\Big[\,f(u_0(y)+h(y)) - f(u_0(y)) - f'(u_0(y))h(y)\,\Big]\,dy .
$$
By the mean value theorem applied to `s ↦ f(u_0(y)+s)`, for each `y` there is `θ_y ∈ (0,1)` with, writing
`ξ_y = u_0(y) + θ_y h(y)`,
$$
f(u_0(y)+h(y)) - f(u_0(y)) = f'(\xi_y)\,h(y),
$$
so the bracket equals `[f'(\xi_y) - f'(u_0(y))]\,h(y)`. Now control `|f'(\xi_y) - f'(u_0(y))|`
*uniformly in `y`*. Since `‖h‖_∞ ≤ 1`, `|\xi_y - u_0(y)| \le |h(y)| \le \|h\|_\infty \le 1`, so both
`u_0(y)` and `ξ_y` lie in the compact set `J_1 = \{ s ∈ ℝ : \operatorname{dist}(s, J) \le 1\}`. On the
compact `J_1`, `f'` is **uniformly continuous**; let
$$
\omega(\delta) := \sup\{\,|f'(s) - f'(t)| : s,t \in J_1,\ |s-t| \le \delta\,\}, \qquad \omega(\delta) \xrightarrow[\delta \to 0^+]{} 0 .
$$
Since `|\xi_y - u_0(y)| \le \|h\|_\infty`, we get `|f'(\xi_y) - f'(u_0(y))| \le \omega(\|h\|_\infty)` for
every `y`. Therefore
$$
|R(x)| \le \int_0^1 |K(x,y)|\,\omega(\|h\|_\infty)\,|h(y)|\,dy \le M_K\,\omega(\|h\|_\infty)\,\|h\|_\infty ,
$$
so `‖R‖_∞ \le M_K\,\omega(\|h\|_\infty)\,\|h\|_\infty` and
$$
\frac{\|F(u_0+h) - F(u_0) - Ah\|_\infty}{\|h\|_\infty} \le M_K\,\omega(\|h\|_\infty) \xrightarrow[\|h\|_\infty \to 0]{} 0 .
$$
This is exactly the definition in (a), so `F` is Fréchet differentiable at `u₀` with `DF(u_0)` given by
`(\ast)`. ∎

### (c) Continuity of `u ↦ DF(u)`

**Claim.** The map `DF : X → \mathcal L(X,X)`, `u ↦ DF(u)`, is continuous (so `F` is `C¹`).

Fix `u₀ ∈ X` and let `u ∈ X` with `‖u - u_0‖_∞ ≤ 1`. For any `h ∈ X`, by `(\ast)`,
$$
[(DF(u) - DF(u_0))h](x) = \int_0^1 K(x,y)\,\big[f'(u(y)) - f'(u_0(y))\big]\,h(y)\,dy ,
$$
so
$$
\big|[(DF(u) - DF(u_0))h](x)\big| \le M_K\,\|h\|_\infty\,\max_{y\in[0,1]} \big|f'(u(y)) - f'(u_0(y))\big| .
$$
Taking the sup over `x` and then over `‖h‖_∞ \le 1`,
$$
\|DF(u) - DF(u_0)\|_{\mathrm{op}} \le M_K\,\max_{y\in[0,1]} \big|f'(u(y)) - f'(u_0(y))\big| . \tag{$\dagger$}
$$
For `‖u - u_0‖_∞ \le 1`, both `u(y)` and `u_0(y)` lie in the compact set `J_1` (as above), on which `f'`
is uniformly continuous with modulus `ω`. Since `|u(y) - u_0(y)| \le \|u - u_0\|_\infty` for every `y`,
$$
\max_{y\in[0,1]} \big|f'(u(y)) - f'(u_0(y))\big| \le \omega(\|u - u_0\|_\infty).
$$
Combining with `(\dagger)`,
$$
\|DF(u) - DF(u_0)\|_{\mathrm{op}} \le M_K\,\omega(\|u - u_0\|_\infty) \xrightarrow[\|u-u_0\|_\infty \to 0]{} 0 .
$$
Hence `u ↦ DF(u)` is continuous at `u₀`; as `u₀` was arbitrary, it is continuous on all of `X`. ∎

**Remark.** The answer to (c) is **yes**, and in fact `F` is continuously Fréchet differentiable (`C¹`).
The proof needed nothing beyond `f ∈ C¹` and the compactness of the ranges `u([0,1])`: compactness turns
plain continuity of `f'` into *uniform* continuity, and that is precisely what converts pointwise Taylor
control into the uniform (sup-norm / operator-norm) estimates required by the Fréchet definition. The
kernel `K` contributes only the harmless constant `M_K = \max|K|`. The same template (linearize inside the
nonlinearity; bound the remainder by the modulus of continuity of the derivative on a compact set) gives
the Fréchet calculus for general Hammerstein/Nemytskii operators on spaces of continuous functions.

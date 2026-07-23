<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98J05: Solving the heat equation on the line by the Fourier transform — the Gaussian heat kernel

## Why It's Hard

The point of the problem is the *method*: the Fourier transform converts `x`-differentiation into
multiplication by `iξ`, so a partial differential equation in `(x,t)` becomes, frequency by frequency, an
ordinary differential equation in `t` alone. The difficulties are not in any single step but in carrying
the chain through cleanly and honestly:

- **The derivative rule (b) requires hypotheses and an integration by parts** — the boundary terms must
  vanish (`f → 0` at `±∞`, with `f, f' ∈ L¹`), or `\widehat{f'} = iξ\hat f` is false. Applying it *twice*
  for `u_{xx}` turns the second `x`-derivative into the multiplier `-ξ²`.
- **Transforming the PDE (c)** needs the legitimacy of differentiating under the integral in `t`
  (`\widehat{u_t} = ∂_t\hat u`) — only then does `u_{xx}=u_t` become `∂_t\hat u = -ξ²\hat u`, a one-line
  ODE with parameter `ξ` and initial value `\hat f(ξ)`.
- **Inverting (d)** is where the real content sits. Solving the ODE gives `\hat u = \hat f\,e^{-tξ²}`, a
  *product* of transforms — so by the convolution theorem `u` is a convolution. But you must **identify
  the second factor**: the function whose Fourier transform is `e^{-tξ²}`. That is a Gaussian integral
  (complete the square), and getting the normalization `\tfrac{1}{2\sqrt{πt}}` and the exponent
  `-x²/(4t)` exactly right is the crux — an off-by-`\sqrt{}` here and the kernel no longer has unit mass.

## The Key Insight

Transform only in `x`. The rule `\widehat{f'} = iξ\hat f` (applied twice) sends `u_{xx} \mapsto -ξ²\hat u`,
collapsing the PDE to the scalar ODE
$$\partial_t \hat u(ξ,t) = -ξ²\,\hat u(ξ,t), \qquad \hat u(ξ,0) = \hat f(ξ) \;\Longrightarrow\; \hat u(ξ,t) = \hat f(ξ)\,e^{-tξ²}.$$
Now read `e^{-tξ²}` as the Fourier transform of the **heat kernel** `G_t(x) = \tfrac{1}{2\sqrt{πt}}e^{-x²/(4t)}`
(a Gaussian integral), so that `\hat u = \hat f\cdot \hat G_t` and the convolution theorem gives
$$u(x,t) = (f \ast G_t)(x) = \frac{1}{2\sqrt{\pi t}}\int_{-\infty}^{\infty} f(y)\,e^{-(x-y)^2/(4t)}\,dy.$$
The whole solution is "diagonalize `∂_x` by Fourier, solve the trivial ODE, invert the Gaussian multiplier
as a convolution."

## Complete Proof

Throughout, use the convention (for `f ∈ L¹(ℝ)`)
$$\hat f(\xi) = \int_{-\infty}^{\infty} f(x)\,e^{-i\xi x}\,dx ,$$
with inversion `f(x) = \frac{1}{2\pi}\int_{-\infty}^{\infty}\hat f(\xi)e^{i\xi x}\,d\xi` and convolution
theorem `\widehat{f\ast g} = \hat f\,\hat g`, where `(f\ast g)(x) = \int_{-\infty}^\infty f(y)g(x-y)\,dy`.

### (a) Definition of the Fourier transform

For `f ∈ L¹(ℝ)`, the integral above converges absolutely (`|f(x)e^{-iξx}| = |f(x)|` is integrable), so
$$\hat f(\xi) = \int_{-\infty}^{\infty} f(x)\,e^{-i\xi x}\,dx$$
is defined for every `ξ ∈ ℝ`; it is a bounded (`\|\hat f\|_\infty \le \|f\|_1`), continuous function of `ξ`
that tends to `0` as `|ξ|\to\infty` (Riemann–Lebesgue).

### (b) Fourier transform of `f'`

Assume `f` is absolutely continuous with `f, f' ∈ L¹(ℝ)`; then `f(x) → 0` as `|x| → \infty`. Integrate by
parts:
$$
\widehat{f'}(\xi) = \int_{-\infty}^{\infty} f'(x)\,e^{-i\xi x}\,dx
= \underbrace{\big[f(x)e^{-i\xi x}\big]_{-\infty}^{\infty}}_{=\,0} - \int_{-\infty}^{\infty} f(x)\,(-i\xi)e^{-i\xi x}\,dx
= i\xi \int_{-\infty}^{\infty} f(x)e^{-i\xi x}\,dx,
$$
so
$$
\boxed{\ \widehat{f'}(\xi) = i\xi\,\hat f(\xi).\ }
$$
Iterating (when `f''∈L¹` etc.), `\widehat{f''}(\xi) = (i\xi)^2\hat f(\xi) = -\xi^2\,\hat f(\xi)`. The
principle: **differentiation in `x` becomes multiplication by `iξ`.**

### (c) Fourier transform of the boundary value problem in `x`

Let `\hat u(\xi,t) = \int_{-\infty}^\infty u(x,t)e^{-i\xi x}\,dx` be the transform in the space variable.
Applying part (b) twice to the `x`-derivatives, and differentiating under the integral sign in `t`,
$$
\widehat{u_{xx}}(\xi,t) = (i\xi)^2\,\hat u(\xi,t) = -\xi^2\,\hat u(\xi,t), \qquad
\widehat{u_t}(\xi,t) = \partial_t\,\hat u(\xi,t).
$$
Hence the PDE `u_{xx} = u_t` transforms, for each fixed `ξ`, into the **first-order linear ODE in `t`**
$$
\boxed{\ \partial_t \hat u(\xi,t) = -\xi^2\,\hat u(\xi,t),\qquad \hat u(\xi,0) = \hat f(\xi),\ }
$$
the initial condition coming from `u(x,0)=f(x)` (so `\hat u(\xi,0)=\hat f(\xi)`).

### (d) Solve and invert — the convolution with the heat kernel

**Solve the ODE.** For each `ξ`, `\partial_t\hat u = -\xi^2\hat u` with `\hat u(\xi,0)=\hat f(\xi)` gives
$$
\hat u(\xi,t) = \hat f(\xi)\,e^{-\xi^2 t}.
$$

**Identify `e^{-tξ²}` as a Fourier transform (the heat kernel).** Seek `G_t` with `\hat G_t(\xi) =
e^{-t\xi^2}`. By inversion,
$$
G_t(x) = \frac{1}{2\pi}\int_{-\infty}^{\infty} e^{-t\xi^2}\,e^{i\xi x}\,d\xi .
$$
Complete the square in the exponent: `-t\xi^2 + i\xi x = -t\big(\xi - \tfrac{ix}{2t}\big)^2 - \tfrac{x^2}{4t}`,
so (shifting the contour and using `\int_{-\infty}^\infty e^{-t\eta^2}\,d\eta = \sqrt{\pi/t}`)
$$
\int_{-\infty}^{\infty} e^{-t\xi^2}e^{i\xi x}\,d\xi = e^{-x^2/(4t)}\int_{-\infty}^{\infty} e^{-t\eta^2}\,d\eta = \sqrt{\tfrac{\pi}{t}}\;e^{-x^2/(4t)} .
$$
Therefore
$$
G_t(x) = \frac{1}{2\pi}\sqrt{\tfrac{\pi}{t}}\;e^{-x^2/(4t)} = \frac{1}{2\sqrt{\pi t}}\;e^{-x^2/(4t)} ,
$$
the **Gaussian heat kernel**. (Check: `\int_{-\infty}^\infty G_t = \hat G_t(0) = 1`.)

**Invert via the convolution theorem.** Since `\hat u(\xi,t) = \hat f(\xi)\,\hat G_t(\xi)` is a product of
transforms, `u(\cdot,t) = f \ast G_t`:
$$
\boxed{\ u(x,t) = (f\ast G_t)(x) = \frac{1}{2\sqrt{\pi t}}\int_{-\infty}^{\infty} f(y)\,e^{-(x-y)^2/(4t)}\,dy,\qquad t>0.\ }
$$
This is the required solution as a convolution. As `t \to 0^+`, `G_t` is an approximate identity, so
`u(\cdot,t) \to f` and the initial condition `u(x,0)=f(x)` is recovered. ∎

**Remark.** The method is diagonalization: the Fourier transform turns `∂_x` into the multiplier `iξ`, so
the heat operator `∂_t - ∂_x^2` becomes `∂_t + \xi^2`, whose solution operator `e^{-t\xi^2}` is a *bounded*
multiplier for every `t > 0`. Inverting that multiplier is exactly convolution against the Gaussian
`G_t`, and the smoothing `e^{-t\xi^2}` (rapid decay in `ξ`) is the frequency-side reason the heat semigroup
instantly turns merely-`L^1` data `f` into a `C^\infty` solution for `t>0`. The same recipe — transform,
solve an ODE in the multiplier, invert as a convolution — solves any constant-coefficient evolution
equation on the line.

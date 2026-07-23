<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95J05: Fundamental solution of d/dt + λ, and solving by convolution

## Why It's Hard

A "fundamental solution" is the right way to *invert* a differential operator, but the inverse lives in
the world of **distributions**, not classical functions. The conceptual hurdle is accepting that the
equation `AE = \delta` makes sense even though `\delta` is not a function and `E` may be only piecewise
smooth: the derivative in `A` must be the *distributional* derivative, where the jump of a step function
manufactures the Dirac mass. Producing `E` for `A = \tfrac{d}{dt} + \lambda` requires seeing that
`H(t)e^{-\lambda t}` has exactly the right discontinuity at `0` to generate `\delta`.

The second idea — using `E` to solve `v' + \lambda v = \varphi` — is the payoff and the subtle part: once
you have a fundamental solution, you solve the inhomogeneous equation for *any* right-hand side by a
single **convolution** `v = E * \varphi`. This works because the constant-coefficient operator commutes
with convolution and `\delta` is the convolution identity. Knowing precisely what a *test function* is
(`C_c^\infty`, compact support) is what guarantees the convolution integral converges and the answer is
smooth.

## The Key Insight

`A` acts on distributions by duality, and a **fundamental solution** is a distribution `E` with
`AE = \delta`. For `A = \tfrac{d}{dt} + \lambda`, the causal candidate `E = H(t)e^{-\lambda t}` works
because the Heaviside jump contributes the delta:

$$E' = \underbrace{\delta}_{\text{jump at }0} - \lambda E \ \Longrightarrow\ E' + \lambda E = \delta.$$

Then for any test function `\varphi`, set `v = E * \varphi`. Since `A` commutes with convolution and
`\delta * \varphi = \varphi`,

$$Av = A(E * \varphi) = (AE) * \varphi = \delta * \varphi = \varphi.$$

So `v(t) = (E*\varphi)(t) = \int_{-\infty}^{t} e^{-\lambda(t-s)}\varphi(s)\,ds` solves `v' + \lambda v = \varphi`,
and the compact support of `\varphi` makes the integral finite and `v` smooth.

## Complete Proof

### (a) Definition of a fundamental solution

Let `A = \sum_\alpha c_\alpha D^\alpha` be a constant-coefficient differential operator. The operator acts
on a distribution `T \in \mathcal D'` through the distributional derivative: `(D^\alpha T)(\varphi) = (-1)^{|\alpha|}T(D^\alpha\varphi)`,
so `AT` is the distribution defined by

$$\langle AT, \varphi\rangle = \sum_\alpha c_\alpha\,(-1)^{|\alpha|}\,\langle T, D^\alpha\varphi\rangle \qquad (\varphi \in \mathcal D).$$

A distribution `E` is called a **fundamental solution** of `A` if

$$\boxed{\ A E = \delta\ }$$

in the sense of distributions, i.e. `\langle AE, \varphi\rangle = \langle \delta, \varphi\rangle = \varphi(0)`
for every test function `\varphi`. (It is a "Green's function" for `A`: the response to a unit point
source at the origin.)

### (b) A fundamental solution of `Au = u' + \lambda u`

Here `A = \tfrac{d}{dt} + \lambda`. Take the **causal** candidate

$$E(t) = H(t)\,e^{-\lambda t},$$

where `H` is the Heaviside step. `E` is locally integrable, hence a distribution. Computing its
distributional derivative by the product rule (with the smooth factor `\psi(t) = e^{-\lambda t}`, `\psi(0)=1`):

$$E' = (H\psi)' = H'\psi + H\psi' = \psi(0)\,\delta + H\,\psi' = \delta - \lambda H e^{-\lambda t} = \delta - \lambda E.$$

Therefore

$$E' + \lambda E = \delta, \qquad \boxed{\ E(t) = H(t)\,e^{-\lambda t}\ }$$

is a fundamental solution of `A = \tfrac{d}{dt} + \lambda`. (The general fundamental solution is
`H(t)e^{-\lambda t} + Ce^{-\lambda t}`, since `e^{-\lambda t}` solves the homogeneous equation; the causal
choice `C=0` is the standard one.)

### (c) Solving `v' + \lambda v = \varphi`

**Test function.** In this one-variable context, a *test function* is an element of
`\mathcal D = C_c^\infty(\mathbb R)`: an infinitely differentiable function `\varphi : \mathbb R \to \mathbb C`
with **compact support** (vanishing outside some bounded interval).

**Solution by convolution.** Set `v = E * \varphi`. Because `A = \tfrac{d}{dt} + \lambda` has constant
coefficients, it commutes with convolution (`(E*\varphi)' = E'*\varphi`), and `\delta` is the identity for
convolution, so

$$v' + \lambda v = (E*\varphi)' + \lambda(E*\varphi) = (E' + \lambda E)*\varphi = \delta * \varphi = \varphi.$$

Explicitly,

$$v(t) = (E * \varphi)(t) = \int_{-\infty}^{\infty} H(t-s)\,e^{-\lambda(t-s)}\,\varphi(s)\,ds
= \boxed{\ e^{-\lambda t}\int_{-\infty}^{t} e^{\lambda s}\,\varphi(s)\,ds.\ }$$

The integral converges (and is finite) because `\varphi` has compact support, so effectively it runs over
`\operatorname{supp}\varphi \cap (-\infty, t]`; consequently `v` is a smooth, genuine function. One checks
directly: differentiating,

$$v'(t) = -\lambda e^{-\lambda t}\int_{-\infty}^t e^{\lambda s}\varphi(s)\,ds + e^{-\lambda t}\,e^{\lambda t}\varphi(t)
= -\lambda v(t) + \varphi(t),$$

so `v' + \lambda v = \varphi`, confirming the convolution solution. ∎

**Remark.** The structure is the general principle of constant-coefficient linear PDE/ODE: a fundamental
solution `E` (with `AE = \delta`) is a *convolution inverse* of `A`, and `v = E * \varphi` solves
`Av = \varphi` for every test function `\varphi` because `A` commutes with convolution and `\delta` is the
convolution unit. Here `E = H(t)e^{-\lambda t}` is exactly the causal Green's function: the Heaviside jump
supplies the unit impulse, and convolving with it is the variation-of-parameters formula
`v(t) = e^{-\lambda t}\int_{-\infty}^t e^{\lambda s}\varphi(s)\,ds` in disguise.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98A04: Convolution of a distribution with a test function — derivatives, smoothness, and a periodic example

## Why It's Hard

The convolution `T ∗ φ` of a distribution with a test function is defined by *pairing `T` against a
translated, reflected copy of `φ`*, so every statement about it must be unwound through the distributional
pairing — there is no integral to differentiate directly when `T` is, say, a delta or a principal value.
The two structural facts to prove are subtle for the same reason:

- **Moving derivatives across the convolution** (`D^α(T∗φ) = (D^αT)∗φ = T∗(D^αφ)`) is really *two*
  different mechanisms wearing one identity. `D^α(T∗φ) = T∗(D^αφ)` is **differentiation under the
  pairing**: you must show the difference quotient of `y ↦ φ(x−y)` converges *in the topology of `𝒟`*
  (uniformly, with all derivatives, supports in a fixed compact set), so that the continuity of `T`
  carries the limit through. Meanwhile `(D^αT)∗φ = T∗(D^αφ)` is the **definition of distributional
  derivative** plus the chain-rule sign `∂_{y_j}φ(x−y) = −(∂_jφ)(x−y)` — pure bookkeeping, no limit.
  Conflating the two is the classic error.
- **Smoothness `T∗φ ∈ C^∞`** is not separate work: it *falls out* of the same differentiation-under-the-
  pairing lemma, applied inductively, once you also check `x ↦ ⟨T, φ(x−·)⟩` is continuous (again because
  `x ↦ φ(x−·)` is continuous into `𝒟`).

Part (c) is a concrete sanity check: a direct periodic integral, where the only trap is expanding
`cos(x−y)` and remembering which of the two period-integrals vanishes.

## The Key Insight

Define
$$(T \ast \varphi)(x) = \big\langle T_y,\; \varphi(x - y)\big\rangle,$$
i.e. `T` applied to the test function `y ↦ φ(x−y)`. Everything rests on one lemma:

> **Lemma.** The map `x ↦ φ(x−\cdot)` is continuous, and difference-differentiable, *as a map into `𝒟`*.

Continuity of this map gives continuity of `T∗φ`; its differentiability (the difference quotient converges
in `𝒟` to `(∂_jφ)(x−\cdot)`) lets the continuous functional `T` differentiate under the pairing:
$$\partial_j (T\ast\varphi)(x) = \langle T_y, (\partial_j\varphi)(x-y)\rangle = (T \ast \partial_j\varphi)(x).$$
Then the **definition of `D^αT`** together with `∂_{y_j}\varphi(x−y) = −(\partial_j\varphi)(x−y)` shows
`(\partial_j T)\ast\varphi = T\ast \partial_j\varphi` as well. Iterating gives both the derivative identity
(a) and, since `D^αφ` is again a test function, infinite differentiability (b). Part (c) is the direct
integral `\sin\ast\cos = \pi\sin`.

## Complete Proof

Notation: for a multiindex `α`, `D^α` is the (distributional or classical) derivative, and the
distributional derivative is defined by `⟨D^α T, ψ⟩ = (-1)^{|α|}⟨T, D^α ψ⟩` for all `ψ ∈ 𝒟`. For
`x ∈ ℝⁿ` write `φ_x(y) := φ(x - y)`.

**`T ∗ φ` is well defined.** For fixed `x`, `φ_x` is smooth and has compact support `x − \operatorname{supp}φ`,
so `φ_x ∈ 𝒟` and `(T∗φ)(x) := ⟨T_y, φ_x(y)⟩ = ⟨T_y, φ(x-y)⟩` makes sense.

### Lemma (the map `x ↦ φ_x` into `𝒟`)

Fix `x₀` and a bounded neighborhood. For `x` in a compact neighborhood `N` of `x₀`, all the supports
`x − \operatorname{supp}φ` lie in one fixed compact set `K = N − \operatorname{supp}φ`. For any
multiindex `β`,
$$D^\beta_y\big[\varphi(x-y)\big] = (-1)^{|\beta|}(D^\beta\varphi)(x-y).$$

*Continuity.* As `x' → x`, `(D^\beta\varphi)(x'-y) → (D^\beta\varphi)(x-y)` **uniformly in `y`** (each
`D^βφ` is uniformly continuous, having compact support), and all supports stay in `K`. So `φ_{x'} → φ_x`
in `𝒟`.

*Differentiability.* For the `j`-th partial, the difference quotient
$$\psi_h(y) := \frac{\varphi(x+he_j - y) - \varphi(x - y)}{h}$$
has supports in a fixed compact set (for small `h`) and, by Taylor's theorem with the uniform continuity
of `D^β\partial_j\varphi`, `D^\beta_y \psi_h \to (-1)^{|\beta|}(D^\beta\partial_j\varphi)(x-y)` uniformly
in `y` as `h → 0`. Hence `ψ_h → (\partial_j\varphi)(x-\cdot)` **in `𝒟`**. ∎(Lemma)

### (a) Derivative identities

Since `T : 𝒟 → ℝ` is linear and **continuous**, it preserves limits in `𝒟`.

**Step 1: differentiate under the pairing.** Using the Lemma's difference-quotient convergence and
continuity of `T`,
$$
\partial_j (T\ast\varphi)(x) = \lim_{h\to 0} \big\langle T_y, \psi_h \big\rangle = \big\langle T_y, (\partial_j\varphi)(x-y)\big\rangle = (T \ast \partial_j\varphi)(x). \tag{1}
$$

**Step 2: move the derivative onto `T`.** By the definition of the distributional derivative `\partial_j T`
(applied to the test function `φ_x = φ(x-\cdot)`) and the chain rule `∂_{y_j}\varphi(x-y) =
-(\partial_j\varphi)(x-y)`,
$$
\big((\partial_j T)\ast\varphi\big)(x) = \big\langle \partial_j T_y, \varphi(x-y)\big\rangle
= -\big\langle T_y, \partial_{y_j}\varphi(x-y)\big\rangle
= \big\langle T_y, (\partial_j\varphi)(x-y)\big\rangle
= (T \ast \partial_j\varphi)(x). \tag{2}
$$

Combining (1) and (2):
$$
\partial_j(T\ast\varphi) = T\ast\partial_j\varphi = (\partial_j T)\ast\varphi .
$$
Iterating over the components of a multiindex `α` (each step lands on another test function / distribution,
so the rule applies again) yields
$$
\boxed{\,D^\alpha(T\ast\varphi) = (D^\alpha T)\ast\varphi = T\ast(D^\alpha\varphi)\,}\qquad\text{for every multiindex } \alpha. \ \blacksquare
$$

### (b) `T ∗ φ ∈ C^∞(ℝⁿ)`

By the Lemma's continuity clause, `x ↦ φ_x` is continuous into `𝒟`, and `T` is continuous, so
`x ↦ (T\ast\varphi)(x) = ⟨T_y, φ(x-y)⟩` is continuous: `T∗φ ∈ C^0`. By (1), `T∗φ` has first partials
`\partial_j(T\ast\varphi) = T\ast\partial_j\varphi`, and since `\partial_j\varphi ∈ 𝒟` is again a test
function, the *same* statement applies to `T\ast\partial_j\varphi`: it too is continuous (so the partials
of `T∗φ` are continuous, giving `T∗φ ∈ C^1`) and itself differentiable. By induction on the order, every
partial derivative
$$
D^\alpha(T\ast\varphi) = T\ast(D^\alpha\varphi)
$$
exists and is continuous, for every multiindex `α`. Therefore `T\ast\varphi ∈ C^\infty(ℝ^n)`. ∎

### (c) Convolution of `f(x)=\sin x` and `g(x)=\cos x` (period `2π`)

By definition,
$$
(f \ast g)(x) = \int_0^{2\pi} f(y)\,g(x-y)\,dy = \int_0^{2\pi} \sin y\,\cos(x-y)\,dy .
$$
Expand `\cos(x-y) = \cos x\cos y + \sin x\sin y`:
$$
(f\ast g)(x) = \cos x\int_0^{2\pi}\sin y\cos y\,dy \;+\; \sin x\int_0^{2\pi}\sin^2 y\,dy .
$$
The two period-integrals are
$$
\int_0^{2\pi}\sin y\cos y\,dy = \tfrac12\int_0^{2\pi}\sin 2y\,dy = 0, \qquad
\int_0^{2\pi}\sin^2 y\,dy = \int_0^{2\pi}\frac{1-\cos 2y}{2}\,dy = \pi .
$$
Hence
$$
\boxed{\,(\sin \ast \cos)(x) = \pi\,\sin x\,.}
$$

**Remark.** Parts (a)–(b) are the *regularization* principle: convolving any distribution with a smooth
compactly supported test function produces a genuine `C^∞` function, and derivatives may be thrown onto
either factor — the analytic engine is differentiation under the pairing, legitimate exactly because
`x ↦ φ(x−\cdot)` is smooth *into `𝒟`* and `T` is continuous on `𝒟`. Part (c) is the Fourier-side shadow of
the same operation: on the circle, `\widehat{f\ast g}(n) = 2\pi\,\hat f(n)\hat g(n)`, and since `\sin` and
`\cos` share only the frequencies `n = \pm 1`, the convolution is again a pure first harmonic — here
exactly `\pi\sin x`.

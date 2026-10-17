<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98A04: Convolution of a distribution with a test function — derivatives, smoothness, and a periodic example

## Why It's Hard

The convolution $T \ast \varphi$ of a distribution with a test function is defined by *pairing $T$ against a
translated, reflected copy of $\varphi$*, so every statement about it must be unwound through the distributional
pairing — there is no integral to differentiate directly when $T$ is, say, a delta or a principal value.
The two structural facts to prove are subtle for the same reason:

- **Moving derivatives across the convolution** ($D^\alpha(T\ast \varphi) = (D^\alpha T)\ast \varphi = T\ast(D^\alpha \varphi)$) is really *two*
  different mechanisms wearing one identity. $D^\alpha(T\ast \varphi) = T\ast(D^\alpha \varphi)$ is **differentiation under the
  pairing**: you must show the difference quotient of $y \mapsto \varphi(x-y)$ converges *in the topology of $\mathcal{D}$*
  (uniformly, with all derivatives, supports in a fixed compact set), so that the continuity of $T$
  carries the limit through. Meanwhile $(D^\alpha T)\ast \varphi = T\ast(D^\alpha \varphi)$ is the **definition of distributional
  derivative** plus the chain-rule sign $\partial_{y_j}\varphi(x-y) = -(\partial_j\varphi)(x-y)$ — pure bookkeeping, no limit.
  Conflating the two is the classic error.
- **Smoothness $T\ast \varphi \in C^\infty$** is not separate work: it *falls out* of the same differentiation-under-the-
  pairing lemma, applied inductively, once you also check $x \mapsto \langle T, \varphi(x-\cdot)\rangle$ is continuous (again because
  $x \mapsto \varphi(x-\cdot)$ is continuous into $\mathcal{D}$).

Part (c) is a concrete sanity check: a direct periodic integral, where the only trap is expanding
$cos(x-y)$ and remembering which of the two period-integrals vanishes.

## The Key Insight

Define
$$(T \ast \varphi)(x) = \big\langle T_y,\; \varphi(x - y)\big\rangle,$$
i.e. $T$ applied to the test function $y \mapsto \varphi(x-y)$. Everything rests on one lemma:

> **Lemma.** The map $x \mapsto \varphi(x-\cdot)$ is continuous, and difference-differentiable, *as a map into $\mathcal{D}$*.

Continuity of this map gives continuity of $T\ast \varphi$; its differentiability (the difference quotient converges
in $\mathcal{D}$ to $(\partial_j\varphi)(x-\cdot)$) lets the continuous functional $T$ differentiate under the pairing:
$$\partial_j (T\ast\varphi)(x) = \langle T_y, (\partial_j\varphi)(x-y)\rangle = (T \ast \partial_j\varphi)(x).$$
Then the **definition of $D^\alpha T$** together with $\partial_{y_j}\varphi(x-y) = -(\partial_j\varphi)(x-y)$ shows
$(\partial_j T)\ast\varphi = T\ast \partial_j\varphi$ as well. Iterating gives both the derivative identity
(a) and, since $D^\alpha \varphi$ is again a test function, infinite differentiability (b). Part (c) is the direct
integral $\sin\ast\cos = \pi\sin$.

## Complete Proof

Notation: for a multiindex $\alpha$, $D^\alpha$ is the (distributional or classical) derivative, and the
distributional derivative is defined by $\langle D^\alpha T, \psi\rangle = (-1)^{|\alpha|}\langle T, D^\alpha \psi\rangle$ for all $\psi \in \mathcal{D}$. For
$x \in \mathbb{R}^{n}$ write $\varphi_x(y) := \varphi(x - y)$.

**$T \ast \varphi$ is well defined.** For fixed $x$, $\varphi_x$ is smooth and has compact support $x - \operatorname{supp}\varphi$,
so $\varphi_x \in \mathcal{D}$ and $(T\ast \varphi)(x) := \langle T_y, \varphi_x(y)\rangle = \langle T_y, \varphi(x-y)\rangle$ makes sense.

### Lemma (the map $x \mapsto \varphi_x$ into $\mathcal{D}$)

Fix $x_{0}$ and a bounded neighborhood. For $x$ in a compact neighborhood $N$ of $x_{0}$, all the supports
$x - \operatorname{supp}\varphi$ lie in one fixed compact set $K = N - \operatorname{supp}\varphi$. For any
multiindex $\beta$,
$$D^\beta_y\big[\varphi(x-y)\big] = (-1)^{|\beta|}(D^\beta\varphi)(x-y).$$

*Continuity.* As $x' \to x$, $(D^\beta\varphi)(x'-y) \to (D^\beta\varphi)(x-y)$ **uniformly in $y$** (each
$D^\beta \varphi$ is uniformly continuous, having compact support), and all supports stay in $K$. So $\varphi_{x'} \to \varphi_x$
in $\mathcal{D}$.

*Differentiability.* For the $j$-th partial, the difference quotient
$$\psi_h(y) := \frac{\varphi(x+he_j - y) - \varphi(x - y)}{h}$$
has supports in a fixed compact set (for small $h$) and, by Taylor's theorem with the uniform continuity
of $D^\beta \partial_j\varphi$, $D^\beta_y \psi_h \to (-1)^{|\beta|}(D^\beta\partial_j\varphi)(x-y)$ uniformly
in $y$ as $h \to 0$. Hence $\psi_h \to (\partial_j\varphi)(x-\cdot)$ **in $\mathcal{D}$**. ∎(Lemma)

### (a) Derivative identities

Since $T : \mathcal{D} \to \mathbb{R}$ is linear and **continuous**, it preserves limits in $\mathcal{D}$.

**Step 1: differentiate under the pairing.** Using the Lemma's difference-quotient convergence and
continuity of $T$,
$$
\partial_j (T\ast\varphi)(x) = \lim_{h\to 0} \big\langle T_y, \psi_h \big\rangle = \big\langle T_y, (\partial_j\varphi)(x-y)\big\rangle = (T \ast \partial_j\varphi)(x). \tag{1}
$$

**Step 2: move the derivative onto $T$.** By the definition of the distributional derivative $\partial_j T$
(applied to the test function $\varphi_x = \varphi(x-\cdot)$) and the chain rule $\partial_{y_j}\varphi(x-y) =
-(\partial_j\varphi)(x-y)$,
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
Iterating over the components of a multiindex $\alpha$ (each step lands on another test function / distribution,
so the rule applies again) yields
$$
\boxed{\,D^\alpha(T\ast\varphi) = (D^\alpha T)\ast\varphi = T\ast(D^\alpha\varphi)\,}\qquad\text{for every multiindex } \alpha. \ \blacksquare
$$

### (b) $T \ast \varphi \in C^\infty(\mathbb{R}^{n})$

By the Lemma's continuity clause, $x \mapsto \varphi_x$ is continuous into $\mathcal{D}$, and $T$ is continuous, so
$x \mapsto (T\ast\varphi)(x) = \langle T_y, \varphi(x-y)\rangle$ is continuous: $T\ast \varphi \in C^0$. By (1), $T\ast \varphi$ has first partials
$\partial_j(T\ast\varphi) = T\ast\partial_j\varphi$, and since $\partial_j\varphi \in \mathcal{D}$ is again a test
function, the *same* statement applies to $T\ast\partial_j\varphi$: it too is continuous (so the partials
of $T\ast \varphi$ are continuous, giving $T\ast \varphi \in C^1$) and itself differentiable. By induction on the order, every
partial derivative
$$
D^\alpha(T\ast\varphi) = T\ast(D^\alpha\varphi)
$$
exists and is continuous, for every multiindex $\alpha$. Therefore $T\ast\varphi \in C^\infty(\mathbb{R}^n)$. ∎

### (c) Convolution of $f(x)=\sin x$ and $g(x)=\cos x$ (period $2\pi$)

By definition,
$$
(f \ast g)(x) = \int_0^{2\pi} f(y)\,g(x-y)\,dy = \int_0^{2\pi} \sin y\,\cos(x-y)\,dy .
$$
Expand $\cos(x-y) = \cos x\cos y + \sin x\sin y$:
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
compactly supported test function produces a genuine $C^\infty$ function, and derivatives may be thrown onto
either factor — the analytic engine is differentiation under the pairing, legitimate exactly because
$x \mapsto \varphi(x-\cdot)$ is smooth *into $\mathcal{D}$* and $T$ is continuous on $\mathcal{D}$. Part (c) is the Fourier-side shadow of
the same operation: on the circle, $\widehat{f\ast g}(n) = 2\pi\,\hat f(n)\hat g(n)$, and since $\sin$ and
$\cos$ share only the frequencies $n = \pm 1$, the convolution is again a pure first harmonic — here
exactly $\pi\sin x$.

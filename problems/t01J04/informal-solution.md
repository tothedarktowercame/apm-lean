<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01J04: Shrinking a neighborhood so its preimage is a manifold with boundary (via Sard)

## Why It's Hard

The obstruction is that `y` itself may be a **critical value** of `f`: then `f^{-1}(y)` need not be a
manifold at all, and neither need `f^{-1}(\overline V)` for a carelessly chosen `V`. So one cannot take `V`
to be just any small ball around `y`. The task is to choose `V` so that its **boundary sphere** is made of
regular data, even though `y` (the center) may be bad. Two ideas have to combine:

- **Reformulate "preimage of a closed ball" as a sublevel set.** A closed ball `\overline V = \{z :
  |z-c|^2 \le \varepsilon^2\}` is `\rho^{-1}\big((-\infty,\varepsilon^2]\big)` for the smooth function
  `\rho(z) = |z-c|^2`. Hence `f^{-1}(\overline V) = h^{-1}\big((-\infty,\varepsilon^2]\big)` where `h =
  \rho\circ f`. The **regular-value theorem for sublevel sets** says this is a manifold *with boundary*
  `h^{-1}(\varepsilon^2)` precisely when `\varepsilon^2` is a **regular value of `h`** — a condition on the
  *boundary radius only*, not on the center `y`.
- **Sard's theorem makes the radius choosable.** The regular values of `h : f^{-1}(U) \to \mathbb R` are
  dense (their complement has measure zero), so a suitable squared-radius can be found *arbitrarily small*,
  guaranteeing both `\overline V \subset U` and `y \in V`.

The subtlety is that `y` need not be a regular value — and it doesn't have to be: only the *radius* `\varepsilon^2`
must be regular, and `y` sits harmlessly in the interior `\{h < \varepsilon^2\}`.

## The Key Insight

Work in a chart centered at `y`, let `h(x) = |f(x) - y|^2` (squared distance in the chart). Then for any
radius `\varepsilon`,
$$
f^{-1}\big(\overline{B(y,\varepsilon)}\big) = \{x : h(x) \le \varepsilon^2\} = h^{-1}\big((-\infty,\varepsilon^2]\big).
$$
By **Sard's theorem** choose `\varepsilon^2 > 0` small and a **regular value** of `h`; by the
**regular-value sublevel theorem**, `\{h \le \varepsilon^2\}` is then a smooth manifold with boundary
`h^{-1}(\varepsilon^2)`. Taking `V = B(y,\varepsilon)` gives `y \in V`, `\overline V \subset U`, and
`f^{-1}(\overline V)` a manifold with boundary. The center `y` may be a critical value of `f`; only the
*sphere radius* needs to be regular.

## Complete Proof

We use two standard facts of differential topology, for a smooth map from a manifold **without** boundary:

- **(Sard's Theorem)** For a smooth map `h : M \to \mathbb R` with `M` a manifold without boundary, the set
  of critical values has Lebesgue measure zero in `\mathbb R`; hence regular values are dense.
- **(Sublevel sets at a regular value)** If `a` is a regular value of a smooth `h : M \to \mathbb R` (`M`
  without boundary), then `M_{\le a} := \{x \in M : h(x) \le a\}` is a smooth manifold with boundary
  `\partial M_{\le a} = h^{-1}(a)`. *(Reason: where `h < a`, `M_{\le a}` is open in `M`, hence a manifold;
  where `h = a`, regularity makes `h` a submersion, so by the submersion normal form `h` is locally a
  coordinate `x_1`, and `\{x_1 \le a\}` is a half-space — a manifold with boundary `\{x_1 = a\}`.)*

**Setup: a chart at `y`.** Let `m = \dim Y`. Choose a smooth chart `\varphi : U' \to \mathbb R^m` on an open
set `U'` with `y \in U' \subseteq U` and `\varphi(y) = 0`. Pick `\delta_0 > 0` so small that the closed ball
`\overline{B(0,\delta_0)} \subset \varphi(U')` and its preimage `\varphi^{-1}\big(\overline{B(0,\delta_0)}\big)`
(compact, since `\varphi` is a homeomorphism and the closed ball is compact) is contained in `U`. This is
possible because `U'` is open and `\varphi(y) = 0`.

**The distance-squared function.** On the open submanifold `W := f^{-1}(U') \subseteq X` (a manifold without
boundary, being open in `X`), define the smooth map
$$
g := \varphi \circ f|_W : W \to \mathbb R^m, \qquad h := |g|^2 : W \to \mathbb R, \quad h(x) = \sum_{i=1}^m g_i(x)^2 .
$$
`h` is smooth and `h \ge 0`. Geometrically `h(x) = |\varphi(f(x))|^2` is the squared chart-distance from
`f(x)` to `y`, so for any radius `\varepsilon \in (0,\delta_0)`,
$$
f^{-1}\big(\varphi^{-1}(\overline{B(0,\varepsilon)})\big) = \{x \in W : |g(x)| \le \varepsilon\} = \{x : h(x) \le \varepsilon^2\} = h^{-1}\big((-\infty,\varepsilon^2]\big), \tag{$\ast$}
$$
using `h \ge 0` to drop the lower bound.

**Choose a small regular radius (Sard).** Apply **Sard's theorem** to `h : W \to \mathbb R`: its critical
values form a measure-zero subset of `\mathbb R`, so regular values are dense. The interval
`(0, \delta_0^2)` has positive length, hence contains a regular value `a` of `h`, with `0 < a < \delta_0^2`.
Set `\varepsilon := \sqrt a \in (0, \delta_0)`.

**Define `V`.** Let
$$
V := \varphi^{-1}\big(B(0,\varepsilon)\big) \subseteq U'.
$$
Then:

- **`y \in V`:** since `\varphi(y) = 0 \in B(0,\varepsilon)` (`\varepsilon > 0`).
- **`\operatorname{cl}(V) \subset U`:** because `\varphi` is a homeomorphism onto `\varphi(U')` and
  `\overline{B(0,\varepsilon)} \subset \varphi(U')`, we have `\operatorname{cl}(V) =
  \varphi^{-1}\big(\overline{B(0,\varepsilon)}\big)`, which is compact (so closed) and, as
  `\varepsilon < \delta_0`, contained in `\varphi^{-1}(\overline{B(0,\delta_0)}) \subset U`.

**The preimage is a manifold with boundary.** By `(\ast)` with `\varepsilon^2 = a`,
$$
f^{-1}\big(\operatorname{cl}(V)\big) = f^{-1}\big(\varphi^{-1}(\overline{B(0,\varepsilon)})\big) = h^{-1}\big((-\infty, a]\big) = \{x \in W : h(x) \le a\}.
$$
Since `a` is a **regular value** of `h` and `W` is a manifold without boundary, the **sublevel-set theorem**
applies: `\{x \in W : h(x) \le a\}` is a smooth manifold with boundary
$$
\partial\, f^{-1}(\operatorname{cl}(V)) = h^{-1}(a) = f^{-1}\big(\varphi^{-1}(\partial B(0,\varepsilon))\big) = f^{-1}(\partial V).
$$

Thus `V` is a neighborhood of `y` with `\operatorname{cl}(V) \subset U` and `f^{-1}(\operatorname{cl}(V))` a
manifold with boundary, as required. ∎

**Remark.** The mechanism is "push the badness to the center, keep the boundary regular." Even if `y` is a
critical value of `f` (so `f^{-1}(y)` is singular), it lives in the *interior* `\{h < a\}` of the preimage,
where no regularity is needed; the manifold-with-boundary structure is required only along the boundary
sphere `f^{-1}(\partial V) = h^{-1}(a)`, and Sard guarantees a radius `a` making *that* level set regular.
The same construction, run with the distance function from a point, is the standard way to produce *regular
domains* `f^{-1}(\overline V)` — compact pieces with controlled boundary — out of arbitrary smooth maps, the
starting point for transversality and cobordism arguments. Note `f^{-1}(\operatorname{cl}(V))` may be empty
(if `y \notin f(X)` for small radius), which is harmlessly a manifold with (empty) boundary.

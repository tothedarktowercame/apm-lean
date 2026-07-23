<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99J05: Minimizing the quadratic ½‖v‖² − f(v) on a Hilbert space — existence, the Euler equation, and its converse

## Why It's Hard

The functional `φ(v) = \tfrac12\|v\|^2 - f(v)` is the model "energy" of the calculus of variations, and the
three parts together are exactly the **variational proof of the Riesz representation theorem**. Each part
has its own pitfall:

- **(a) Existence and uniqueness of a minimizer.** Coercivity (`φ(v) → +∞` as `‖v‖ → ∞`) gives a lower
  bound and a minimizing sequence, but in *infinite* dimensions a bounded sequence need not have a
  convergent subsequence — closed bounded sets are not compact. You cannot just "extract a convergent
  subsequence." The decisive tool is the **parallelogram law**, which turns the gap between a minimizing
  sequence and the infimum into control of `‖v_n - v_m‖`, making the sequence **Cauchy**; completeness then
  delivers the limit. Missing that the parallelogram identity (i.e. the Hilbert, not merely Banach,
  structure) is what rescues compactness is the classic error.
- **(b) The Euler–Lagrange equation.** At a minimizer the directional derivative must vanish in *every*
  direction. Restricting `φ` to the line `t ↦ u + tv` gives a one-variable quadratic whose derivative at
  `t = 0` must be zero; this yields `(u,v) = f(v)` for all `v`. The trap is forgetting that `v` ranges over
  *all* of `V` (both signs of `t`), which is what upgrades "`≥ 0`" to an equality.
- **(c) Sufficiency.** The converse is a one-line *completion of the square*: the condition `(u,v)=f(v)`
  collapses the cross term and leaves `φ(w) = φ(u) + \tfrac12\|w-u\|^2`, which is `≥ φ(u)` with equality
  only at `w = u`. The same identity simultaneously re-proves uniqueness.

## The Key Insight

Everything is one algebraic identity, **completion of the square**. If `u` satisfies `(u,v) = f(v)` for all
`v`, then for every `w`,
$$\varphi(w) = \varphi(u) + \tfrac12\|w - u\|^2,$$
so `u` is the unique minimizer. Existence of such a `u` (part a) is forced by the **parallelogram law**:
for a minimizing sequence,
$$\tfrac14\|v_n - v_m\|^2 = \varphi(v_n) + \varphi(v_m) - 2\varphi\!\Big(\tfrac{v_n+v_m}{2}\Big) \le \varphi(v_n)+\varphi(v_m) - 2m \to 0,$$
so it is Cauchy and converges (completeness). The Euler equation `(u,v) = f(v)` (part b) is just
`\tfrac{d}{dt}\varphi(u+tv)\big|_{t=0} = 0`. The three parts are existence ⇒ Euler equation ⇒ (conversely)
the Euler equation characterizes the minimizer — i.e. the Riesz vector built variationally.

## Complete Proof

`V` is a real Hilbert space with inner product `(\cdot,\cdot) = (\cdot,\cdot)_V` and norm `\|v\| = (v,v)^{1/2}`;
`f ∈ V'` is a bounded linear functional (`|f(v)| \le \|f\|\,\|v\|`); and `φ(v) = \tfrac12\|v\|^2 - f(v)`.

### (a) A unique minimizer exists

**`φ` is bounded below (coercive).** For all `v`, using `f(v) \le \|f\|\,\|v\|`,
$$
\varphi(v) = \tfrac12\|v\|^2 - f(v) \ge \tfrac12\|v\|^2 - \|f\|\,\|v\| = \tfrac12(\|v\| - \|f\|)^2 - \tfrac12\|f\|^2 \ge -\tfrac12\|f\|^2 .
$$
Hence `m := \inf_{v\in V}\varphi(v) \ge -\tfrac12\|f\|^2 > -\infty`. Choose a **minimizing sequence**
`(v_n)` with `\varphi(v_n) \to m`.

**Key identity (parallelogram law).** For any `v_n, v_m`, the linear terms in `f` cancel and the
parallelogram law `\|v_n+v_m\|^2 + \|v_n-v_m\|^2 = 2\|v_n\|^2 + 2\|v_m\|^2` gives
$$
\varphi(v_n) + \varphi(v_m) - 2\,\varphi\!\Big(\tfrac{v_n+v_m}{2}\Big)
= \tfrac12\big(\|v_n\|^2 + \|v_m\|^2\big) - \tfrac14\|v_n+v_m\|^2
= \tfrac14\|v_n - v_m\|^2 . \tag{$\ast$}
$$
*(Check of the middle equality: `2\varphi(\tfrac{v_n+v_m}{2}) = \tfrac14\|v_n+v_m\|^2 - (f(v_n)+f(v_m))`,
and `\varphi(v_n)+\varphi(v_m) = \tfrac12(\|v_n\|^2+\|v_m\|^2) - (f(v_n)+f(v_m))`; subtracting cancels the
`f` terms.)*

**The sequence is Cauchy.** Since `\tfrac{v_n+v_m}{2} ∈ V`, we have `\varphi(\tfrac{v_n+v_m}{2}) \ge m`, so
`(\ast)` yields
$$
\tfrac14\|v_n - v_m\|^2 \le \varphi(v_n) + \varphi(v_m) - 2m \xrightarrow[n,m\to\infty]{} m + m - 2m = 0 .
$$
Thus `(v_n)` is Cauchy. As `V` is **complete**, `v_n \to u` for some `u ∈ V`. The map `φ` is continuous
(the norm and `f` are continuous), so
$$
\varphi(u) = \lim_{n\to\infty}\varphi(v_n) = m ,
$$
i.e. `u` is a minimizer.

**Uniqueness.** If `u, u'` both attain `m`, apply `(\ast)` to the pair `u, u'`:
$$
\tfrac14\|u - u'\|^2 = \varphi(u) + \varphi(u') - 2\varphi\!\Big(\tfrac{u+u'}{2}\Big) \le 2m - 2m = 0 ,
$$
so `\|u-u'\| = 0`, `u = u'`. Hence the minimizer is unique. ∎

### (b) A minimizer satisfies `(u,v) = f(v)` for all `v`

Fix `v ∈ V` and consider the real function of one variable
$$
g(t) := \varphi(u + tv) = \tfrac12\|u+tv\|^2 - f(u+tv)
= \tfrac12\|u\|^2 + t\,(u,v) + \tfrac{t^2}{2}\|v\|^2 - f(u) - t\,f(v) .
$$
Because `u` minimizes `φ` over all of `V`, in particular `g(t) = \varphi(u+tv) \ge \varphi(u) = g(0)` for
every `t ∈ ℝ`, so `g` has a minimum at the interior point `t = 0`. Since `g` is differentiable,
$$
0 = g'(0) = (u,v) - f(v) .
$$
As `v ∈ V` was arbitrary, `(u,v) = f(v)` for all `v ∈ V`. ∎

### (c) Conversely, such a `u` minimizes `φ`

Suppose `u ∈ V` satisfies `(u,v) = f(v)` for all `v ∈ V`. Let `w ∈ V` be arbitrary and write `w = u + v`
with `v = w - u`. Then
$$
\varphi(w) = \tfrac12\|u+v\|^2 - f(u+v) = \tfrac12\|u\|^2 + (u,v) + \tfrac12\|v\|^2 - f(u) - f(v) .
$$
Using the hypothesis `f(v) = (u,v)`, the cross terms cancel:
$$
\varphi(w) = \underbrace{\tfrac12\|u\|^2 - f(u)}_{=\,\varphi(u)} + \tfrac12\|v\|^2 = \varphi(u) + \tfrac12\|w - u\|^2 .
$$
Therefore `\varphi(w) \ge \varphi(u)` for all `w ∈ V`, with equality iff `\|w-u\| = 0`, i.e. `w = u`. Hence
`u` is the (unique) minimum point of `φ`. ∎

**Remark.** The three parts are precisely the **variational proof of the Riesz representation theorem**:
(a) produces a vector `u`, (b) shows it represents `f` as `f(v) = (u,v)`, and (c) shows this representation
property is equivalent to minimizing the energy `φ`. Uniqueness of the minimizer is uniqueness of the Riesz
vector. The two structural facts that power the argument are exactly the two defining features of Hilbert
space: the **parallelogram law** (which is what makes minimizing sequences Cauchy and rescues the failure
of compactness in infinite dimensions) and **completeness** (which supplies the limit). In Banach spaces
that are not Hilbert, `(\ast)` fails and a minimizer need not exist.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t94A04: Two simply connected opens with connected overlap glue to a simply connected space

## Why It's Hard

This is the "simply connected" special case of van Kampen, but we are forbidden from quoting van Kampen and
must build the homotopy **by hand**. The obstacle is that a loop `\alpha` in `X = U \cup V` weaves back and
forth between `U` and `V`, so it lies in neither simply connected piece as a whole; one cannot directly apply
simple-connectivity of `U` or of `V`. The fix is to *chop* the loop into short arcs, each living in a single
piece — possible by a compactness/Lebesgue-number argument — but a single arc is not a loop, so
simple-connectivity does not yet apply to it. The decisive idea is to run a **spoke** from the basepoint to
each chopping point, *staying inside the overlap* `U \cap V`, which converts each arc into an honest loop
contained in one of `U, V`. Here the hypotheses pull their weight: the chopping points land in `U \cap V`
(they are where `\alpha` switches sides), and `U \cap V` being **path-connected** is exactly what makes the
spokes exist while remaining in *both* `U` and `V`.

## The Key Insight

Pick a basepoint `x_0 \in U \cap V`. For a loop `\alpha` at `x_0`:

1. `\alpha^{-1}(U), \alpha^{-1}(V)` is an open cover of the compact `[0,1]`; by the **Lebesgue number lemma**
   there is a partition `0 = t_0 < t_1 < \dots < t_n = 1` with each arc `\alpha|_{[t_{k-1}, t_k]}` mapped
   entirely into `U` or entirely into `V`. After merging adjacent arcs on the same side, each breakpoint
   `\alpha(t_k)` lies in `U \cap V` (it borders an arc in `U` and one in `V`).
2. Since `U \cap V` is path-connected, choose **spokes** `\gamma_k` from `x_0` to `\alpha(t_k)` *inside*
   `U \cap V` (and `\gamma_0 = \gamma_n = ` constant at `x_0`).
3. Inserting the null-homotopic pairs `\gamma_k^{-1}\gamma_k` between the arcs,
   `\alpha \simeq \beta_1 \beta_2 \cdots \beta_n` where `\beta_k = \gamma_{k-1}\,(\alpha|_{[t_{k-1},t_k]})\,\gamma_k^{-1}`
   is a **loop at `x_0` contained in `U`** (or in `V`): the middle arc lies in `U` and the spokes lie in
   `U \cap V \subseteq U`. As `U` and `V` are simply connected, each `\beta_k` is null-homotopic, so
   `\alpha` is. Hence `X` is simply connected.

## Complete Proof

Let `X = U \cup V` with `U, V` open, path-connected, and simply connected, and `U \cap V \ne \varnothing`
path-connected. Fix `x_0 \in U \cap V`.

**Step 0 — `X` is path-connected.** `U` and `V` are path-connected and share the nonempty `U \cap V`, so
`U \cup V = X` is path-connected.

**Step 1 — Subdivide a loop (Lebesgue).** Let `\alpha : [0,1] \to X` be a loop with `\alpha(0) = \alpha(1) = x_0`.
Since `\alpha` is continuous, `\alpha^{-1}(U)` and `\alpha^{-1}(V)` are open and cover the compact metric
space `[0,1]`. By the **Lebesgue number lemma** there is `\delta > 0` such that every subinterval of length
`< \delta` maps into `U` or into `V`. Choose a partition `0 = t_0 < t_1 < \dots < t_n = 1` of mesh `< \delta`;
then for each `k`,

$$\alpha\big([t_{k-1}, t_k]\big) \subseteq U \quad\text{or}\quad \alpha\big([t_{k-1}, t_k]\big) \subseteq V.$$

If two consecutive arcs both map into `U` (or both into `V`), delete the breakpoint between them (merge the
arcs); repeating, we may assume **consecutive arcs lie in different sets**. Then each interior breakpoint
`\alpha(t_k)` (`1 \le k \le n-1`) is in the closure of an arc in `U` and an arc in `V`, so
`\alpha(t_k) \in U \cap V`. Also `\alpha(t_0) = \alpha(t_n) = x_0 \in U \cap V`.

**Step 2 — Spokes through the overlap.** For `1 \le k \le n-1`, since `\alpha(t_k) \in U \cap V`, `x_0 \in U \cap V`,
and `U \cap V` is path-connected, choose a path

$$\gamma_k : [0,1] \to U \cap V, \qquad \gamma_k(0) = x_0,\ \gamma_k(1) = \alpha(t_k).$$

Set `\gamma_0 = \gamma_n = ` the constant path at `x_0`. Let `\alpha_k` denote the `k`-th arc
`\alpha|_{[t_{k-1}, t_k]}` reparametrized to `[0,1]`, a path from `\alpha(t_{k-1})` to `\alpha(t_k)`.

**Step 3 — Decompose `\alpha` into loops, one per piece.** Up to the standard reparametrization homotopy,
`\alpha \simeq \alpha_1 \cdot \alpha_2 \cdots \alpha_n`. Insert the cancelling pairs `\gamma_k^{-1} \cdot \gamma_k`
(each homotopic to a constant) between consecutive arcs:

$$\alpha \ \simeq\ \big(\gamma_0\,\alpha_1\,\gamma_1^{-1}\big)\cdot\big(\gamma_1\,\alpha_2\,\gamma_2^{-1}\big)\cdots\big(\gamma_{n-1}\,\alpha_n\,\gamma_n^{-1}\big)
\ =\ \beta_1 \cdot \beta_2 \cdots \beta_n,$$

where `\beta_k = \gamma_{k-1}\,\alpha_k\,\gamma_k^{-1}`. Each `\beta_k` is a **loop based at `x_0`**: `\gamma_{k-1}`
runs `x_0 \to \alpha(t_{k-1})`, `\alpha_k` runs `\alpha(t_{k-1}) \to \alpha(t_k)`, and `\gamma_k^{-1}` runs
`\alpha(t_k) \to x_0`.

**Step 4 — Each loop lies in a simply connected set.** Suppose `\alpha_k` has image in `U` (the `V` case is
symmetric). The spokes `\gamma_{k-1}, \gamma_k` have image in `U \cap V \subseteq U`. Hence
`\operatorname{im}(\beta_k) \subseteq U`. Since `U` is **simply connected**, `\beta_k` is null-homotopic
(rel `x_0`). Likewise any `\beta_k` whose middle arc lies in `V` is a loop in `V` and is null-homotopic.

**Step 5 — Conclude.** Therefore

$$\alpha \ \simeq\ \beta_1 \cdots \beta_n \ \simeq\ (\text{const}) \cdots (\text{const}) \ \simeq\ \text{const}.$$

Every loop at `x_0` is null-homotopic, so `\pi_1(X, x_0)` is trivial; together with Step 0,

$$\boxed{\ X \text{ is simply connected.}\ }\qquad\blacksquare$$

**Remark.** The construction is exactly the engine inside van Kampen, exposed by hand. Three hypotheses each
play their role: simple-connectivity of `U` and `V` kills the pieces; the **Lebesgue number lemma**
(compactness of `[0,1]`) makes the pieces small enough to lie in one set; and **path-connectivity of the
overlap** `U \cap V` provides spokes that lie in *both* `U` and `V`, so attaching them to an arc never pushes
it out of the piece it lives in. Drop the connectivity of `U \cap V` and the conclusion fails: `S^1` is the
union of two simply connected open arcs whose intersection is *two* components, and `S^1` is not simply
connected — the overlap's disconnectedness is precisely what lets a loop "wind."

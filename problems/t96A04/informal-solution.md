<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96A04: The space of [0,1]-valued continuous functions is not compact

## Why It's Hard

The space `C` is *complete* (a uniform limit of continuous functions is continuous, and the value
constraint `[0,1]` is closed) and *bounded* (`d(f,g) \le 1` always), so it satisfies the two properties that
in *finite-dimensional* spaces would force compactness — Heine–Borel makes "closed and bounded" equal
"compact" in `\mathbb R^n`. The trap is to conclude compactness from these. But `C` is **infinite-dimensional**,
and there Heine–Borel fails: a closed bounded set need not be **totally bounded**. To disprove compactness one
must exhibit the failure of total boundedness concretely — an infinite family of functions that stay a fixed
distance apart, hence have no convergent subsequence. The difficulty is constructing such a "spread out"
sequence inside the constraint `f : [0,1] \to [0,1]`.

## The Key Insight

Compactness of a metric space implies **sequential compactness** and **total boundedness**. We exhibit a
sequence in `C` that is **`1`-separated** — pairwise sup-distance `1` — so it has no Cauchy (hence no
convergent) subsequence. Use disjoint-support "unit bumps": let `\varphi_n` be the triangular function of
height `1` supported on `[\tfrac{1}{n+1}, \tfrac1n]` and `0` elsewhere. These are continuous, map into
`[0,1]`, and the supports are pairwise disjoint, so at the peak `x_n` of `\varphi_n`, `\varphi_n(x_n) = 1`
while `\varphi_m(x_n) = 0` (`m \ne n`); hence

$$d(\varphi_n, \varphi_m) = \sup_x |\varphi_n(x) - \varphi_m(x)| = 1 \qquad (n \ne m).$$

A `1`-separated infinite sequence has no convergent subsequence, so `C` is not sequentially compact —
**`C` is not compact**.

## Complete Proof

We **disprove** compactness of `(C, d)`, `d(f,g) = \sup_{x\in[0,1]}|f(x) - g(x)|`.

**Construction of a separated sequence.** For each `n \ge 1`, let `I_n = [\tfrac{1}{n+1}, \tfrac1n]` (these
intervals have pairwise disjoint interiors and lie in `(0,1]`), with midpoint `x_n`. Define
`\varphi_n : [0,1] \to [0,1]` to be the continuous "tent": it rises linearly from `0` at `\tfrac{1}{n+1}` to
`1` at `x_n`, descends linearly to `0` at `\tfrac1n`, and is `0` outside `I_n`. Each `\varphi_n` is continuous
with values in `[0,1]`, so `\varphi_n \in C`.

**The sequence is `1`-separated.** Fix `n \ne m`. The supports `I_n, I_m` are essentially disjoint
(`\operatorname{int} I_n \cap \operatorname{int} I_m = \varnothing`), so `x_n \in \operatorname{int} I_n`
lies outside `I_m`, giving `\varphi_n(x_n) = 1` and `\varphi_m(x_n) = 0`. Hence

$$d(\varphi_n, \varphi_m) = \sup_{x}|\varphi_n(x) - \varphi_m(x)| \ge |\varphi_n(x_n) - \varphi_m(x_n)| = 1,$$

and since both functions take values in `[0,1]`, `|\varphi_n - \varphi_m| \le 1` everywhere, so
`d(\varphi_n, \varphi_m) = 1`.

**No convergent subsequence.** Suppose some subsequence `(\varphi_{n_k})` converged in `C`. Then it would be
Cauchy: for `\varepsilon = \tfrac12` there would be `K` with `d(\varphi_{n_j}, \varphi_{n_k}) < \tfrac12` for
`j, k \ge K`. But `d(\varphi_{n_j}, \varphi_{n_k}) = 1` for `j \ne k`, a contradiction. So `(\varphi_n)` has no
convergent subsequence.

**Conclusion.** A compact metric space is sequentially compact (every sequence has a convergent subsequence).
Since the sequence `(\varphi_n)` in `C` has no convergent subsequence, `C` is **not** sequentially compact,
hence

$$\boxed{\ C \text{ is not compact.}\ }\qquad\blacksquare$$

**Remark.** `C` is complete and bounded but **not totally bounded** — the family `\{\varphi_n\}` is an infinite
`1`-separated set, so no finite collection of `\tfrac12`-balls can cover `C`. This is the hallmark of
infinite-dimensional metric spaces: Heine–Borel ("closed and bounded `\Rightarrow` compact") *fails*, exactly
because boundedness no longer implies total boundedness. (Equally, `f_n(x) = x^n` works: it converges
pointwise to the discontinuous function `0`-on-`[0,1)`, `1`-at-`1`, so no subsequence can converge uniformly —
a uniform limit would be continuous.) Compactness in function spaces requires the stronger
equicontinuity + pointwise-boundedness of Arzelà–Ascoli, which `C` (containing arbitrarily steep bumps) badly
violates.

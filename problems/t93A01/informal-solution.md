<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93A01: An open set is a cozero set — Fσ structure plus a weighted Urysohn sum

## Why It's Hard

The goal of part (b) is to manufacture a continuous function that is **strictly positive on `U` and zero off
`U`** — i.e. to realize the open set `U` as the "positivity set" (cozero set) of a continuous function. A
single application of Urysohn's lemma gives a function that is `1` on one closed set and `0` on another, but
it cannot be positive on *all* of `U` at once while staying continuous, because `U` is open and its
"boundary behavior" must be handled. The resolution is a two-stage strategy that part (a) sets up: first
exhibit `U` as a **countable union of closed sets** (an `F_\sigma`), then build the desired function as a
**convergent weighted sum** of Urysohn functions, one for each closed piece. The subtleties are getting the
`F_\sigma` decomposition (which needs *regularity* to shrink neighborhoods inside `U`, and the *countable
basis* to do so countably) and ensuring the infinite sum converges to a continuous function (weights `2^{-n}`
force uniform convergence).

## The Key Insight

- **(a)** `X` is regular (normal + Hausdorff), so each `x \in U` has a basis element `B` with `x \in B` and
  `\overline B \subseteq U`. Collecting these over the countable basis, `U = \bigcup_n \overline{B_n}` (the
  union over `\{n : \overline{B_n} \subseteq U\}`) — a countable union of closed sets.
- **(b)** Write `U = \bigcup_{n\ge1} C_n` with `C_n` closed. Each `C_n` and the closed set `X \setminus U` are
  disjoint, so Urysohn gives continuous `f_n : X \to [0,1]` with `f_n \equiv 1` on `C_n`, `f_n \equiv 0` off
  `U`. Then `f = \sum_{n\ge1} 2^{-n} f_n` converges uniformly (continuous), is `0` off `U`, and at any
  `x \in U` lies in some `C_m`, giving `f(x) \ge 2^{-m} f_m(x) = 2^{-m} > 0`.

## Complete Proof

`X` is normal and Hausdorff (so `T_1`, hence **regular**) with a countable basis `\{B_n\}_{n\ge1}`, and
`U \subseteq X` is open.

### (a) `U` is a countable union of closed sets

For each `x \in U`, regularity gives an open set `W` with `x \in W \subseteq \overline W \subseteq U` (`x`
and the closed set `X \setminus U` are separated). Since `\{B_n\}` is a basis, choose `n` with
`x \in B_n \subseteq W`; then `\overline{B_n} \subseteq \overline W \subseteq U`. So every point of `U` lies
in some basis element whose closure is contained in `U`.

Let `A = \{\, n : \overline{B_n} \subseteq U \,\}` (a subset of `\mathbb N`, hence countable). By the above,
`U \subseteq \bigcup_{n \in A} B_n`, and conversely `\bigcup_{n\in A}\overline{B_n} \subseteq U`. Combining,

$$U = \bigcup_{n \in A} \overline{B_n},$$

a **countable union of closed sets** (each `\overline{B_n}` is closed). ∎

### (b) A continuous `f` positive exactly on `U`

Write the decomposition from (a) as `U = \bigcup_{n=1}^\infty C_n` with each `C_n` closed and `C_n \subseteq U`
(re-index `A`; if `A` is finite or empty, the argument is the same or `f \equiv 0`).

**Urysohn functions.** For each `n`, the sets `C_n` and `X \setminus U` are **disjoint closed** sets (since
`C_n \subseteq U`). By **Urysohn's lemma** (`X` is normal), there is a continuous

$$f_n : X \to [0,1], \qquad f_n \equiv 1 \text{ on } C_n, \qquad f_n \equiv 0 \text{ on } X \setminus U.$$

**The weighted sum.** Define

$$f = \sum_{n=1}^\infty \frac{1}{2^n}\, f_n.$$

Since `0 \le f_n \le 1`, the series is dominated by `\sum_n 2^{-n} = 1`, so by the Weierstrass `M`-test it
converges **uniformly**; a uniform limit of continuous functions is continuous, so `f` is continuous, and
`0 \le f \le 1`.

**`f = 0` off `U`.** If `x \notin U`, then `f_n(x) = 0` for every `n` (each `f_n` vanishes on
`X \setminus U`), so `f(x) = 0`.

**`f > 0` on `U`.** If `x \in U`, then `x \in C_m` for some `m` (as `U = \bigcup_n C_n`), so `f_m(x) = 1`.
All terms are nonnegative, hence

$$f(x) \ge \frac{1}{2^m} f_m(x) = \frac{1}{2^m} > 0.$$

Therefore `f : X \to [0,1]` is continuous with `f(x) > 0` for `x \in U` and `f(x) = 0` for `x \notin U`.

$$\boxed{\ U = \{x : f(x) > 0\}\ \text{for a continuous } f : X \to [0,1].\ }\qquad\blacksquare$$

**Remark.** The two parts combine into the statement that, in a normal space, **open `F_\sigma` sets are
exactly cozero sets** (`\{f > 0\}` for continuous `f`). Part (a) supplies the `F_\sigma` structure using the
regularity (to shrink neighborhoods inside `U`) and second countability (to do it with countably many pieces)
— in a general normal space an open set need not be `F_\sigma`, which is why the countable basis hypothesis
matters. Part (b) is the standard "sum of bump functions" construction: Urysohn handles each closed piece, and
the geometric weights `2^{-n}` guarantee the sum is continuous while keeping it strictly positive wherever any
single piece is active. (This is precisely the trick used to build partitions of unity and to show metric/
perfectly normal spaces have every open set cozero.)

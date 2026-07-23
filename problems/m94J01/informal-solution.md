<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94J01: A moving high-order delta — converges in 𝒟′, diverges in 𝒮′

## Why It's Hard

The sequence `T_n = \delta_n^{(n)}` changes in *two* ways at once: the singularity moves to the
right (centered at `x=n`), and the order of differentiation grows (the `n`-th derivative). A limit
in a distribution space means `\langle T_n, f\rangle = (-1)^n f^{(n)}(n)` converges for every test
function `f`, and the answer depends entirely on **which class of test functions** you use — this is
the whole subtlety. The two Schwartz spaces `\mathcal D'` and `\mathcal S'` are dual to test
functions with very different behavior at infinity (`C_c^\infty` vs. rapidly decreasing), and the
moving-and-differentiating delta interacts with those two behaviors in opposite ways.

The trap is to expect the same answer for both. In `\mathcal D'` the *location* is what matters and
the sequence collapses to `0`; in `\mathcal S'` the *growing order* is what matters and the sequence
fails to converge at all. Seeing that these are two distinct mechanisms — and producing an explicit
Schwartz function that exposes the second — is the hard part.

## The Key Insight

`\langle \delta_n^{(n)}, f\rangle = (-1)^n f^{(n)}(n)`. Two facts about test functions decide everything:

- **In `\mathcal D'` (test functions `f \in C_c^\infty`):** `f` has *compact* support `\subseteq[-R,R]`.
  Once `n > R`, the point `n` is outside the support, so `f^{(n)}(n) = 0`. The moving singularity
  simply *escapes* the support, and `\langle T_n, f\rangle = 0` for all large `n`. **Limit `= 0`.**

- **In `\mathcal S'` (test functions `f \in \mathcal S`):** Schwartz functions do **not** vanish past
  any point, and there is no bound forcing the high derivative `f^{(n)}(n)` to decay. One can *build*
  a Schwartz `f` with `f^{(n)}(n) = 1` for every `n`, using disjoint bumps `\sim (x-n)^n/n!` near each
  integer (whose `n`-th derivative at the center is exactly `1`), with `1/n!` making the function
  rapidly decreasing. Then `\langle T_n, f\rangle = (-1)^n` oscillates and **has no limit.**

The single phrase that captures it: `\mathcal D'` convergence only needs the *support to escape*;
`\mathcal S'` convergence would additionally need control of *arbitrarily high derivatives at
infinity*, and that control does not exist.

## Complete Proof

For `f` a test function, `\langle \delta_n^{(n)}, f\rangle = (-1)^n f^{(n)}(n)`.

### Part 1 — In `\mathcal D'`: the limit is `0`

Let `f \in \mathcal D = C_c^\infty(\mathbb R)`, with `\operatorname{supp} f \subseteq [-R, R]`. For any
integer `n > R`, the point `n` lies outside `\operatorname{supp} f`, so `f` and all its derivatives
vanish there; in particular `f^{(n)}(n) = 0`. Hence

$$\langle \delta_n^{(n)}, f\rangle = (-1)^n f^{(n)}(n) = 0 \qquad \text{for all } n > R,$$

so `\langle \delta_n^{(n)}, f\rangle \to 0`. Since this holds for every `f \in \mathcal D`, the
sequence converges in `\mathcal D'` (the limit is automatically a distribution, by the completeness
of `\mathcal D'`), and

$$\boxed{\ \delta_n^{(n)} \longrightarrow 0 \quad \text{in } \mathcal D'. \ }$$

### Part 2 — In `\mathcal S'`: no limit exists

If the sequence converged in `\mathcal S'`, its limit would have to be the zero distribution: `\mathcal D`
is dense in `\mathcal S`, and the `\mathcal S'`-limit restricted to `\mathcal D` must agree with the
`\mathcal D'`-limit, which is `0` by Part 1. So it suffices to exhibit a single `f \in \mathcal S` for
which `\langle \delta_n^{(n)}, f\rangle = (-1)^n f^{(n)}(n)` does **not** tend to `0`.

**Construction.** Fix `\chi \in C_c^\infty(\mathbb R)` with `\chi \equiv 1` on `[-\tfrac14,\tfrac14]`,
`\operatorname{supp}\chi \subseteq (-\tfrac12, \tfrac12)`, and `0 \le \chi \le 1`. Define

$$f(x) = \sum_{n=1}^{\infty} g_n(x), \qquad g_n(x) = \frac{(x-n)^n}{n!}\,\chi(x-n).$$

The bumps have disjoint supports `\operatorname{supp} g_n \subseteq (n-\tfrac12, n+\tfrac12)`, so near any
integer `n` only the single term `g_n` is nonzero.

**The high derivative at `n` is `1`.** Near `x = n` (within `\tfrac14`), `\chi(x-n) \equiv 1`, so
`g_n(x) = (x-n)^n/n!`, a polynomial whose `n`-th derivative is the constant `1`. Hence

$$f^{(n)}(n) = g_n^{(n)}(n) = 1 \qquad \text{for every } n,$$

and therefore `\langle \delta_n^{(n)}, f\rangle = (-1)^n f^{(n)}(n) = (-1)^n`, which oscillates between
`+1` and `-1` and does not converge.

**`f` is Schwartz.** We must check `\sup_x |x|^a |f^{(b)}(x)| < \infty` for all `a, b \ge 0`. Because the
supports are disjoint, `f^{(b)}` equals a single `g_n^{(b)}` on each interval `(n-\tfrac12, n+\tfrac12)`,
where `|x| \le 2n`. By the Leibniz rule, for `n \ge b`,

$$g_n^{(b)}(x) = \frac{1}{n!}\sum_{j=0}^{b}\binom{b}{j}\,\frac{n!}{(n-b+j)!}\,(x-n)^{n-b+j}\,\chi^{(j)}(x-n),$$

and on `|x-n| < \tfrac12` each term is bounded by `\binom{b}{j} M_j\,(1/2)^{\,n-b+j}/(n-b+j)!` (with
`M_j = \sup|\chi^{(j)}|`). For fixed `b` the dominant term (`j=0`) gives

$$|g_n^{(b)}(x)| \le C_b\,\frac{(1/2)^{\,n-b}}{(n-b)!}\qquad (n \ge b),$$

which decays **super-exponentially** in `n`. Hence

$$|x|^a\,|f^{(b)}(x)| \le (2n)^a\, C_b\,\frac{(1/2)^{\,n-b}}{(n-b)!} \xrightarrow[n\to\infty]{} 0,$$

and is bounded over all `n`. So `\sup_x |x|^a|f^{(b)}(x)| < \infty` for every `a, b`, i.e.
`f \in \mathcal S`.

**Conclusion.** For this `f \in \mathcal S`, `\langle \delta_n^{(n)}, f\rangle = (-1)^n \not\to 0`, so the
sequence cannot converge in `\mathcal S'`:

$$\boxed{\ \delta_n^{(n)} \text{ has \emph{no} limit in } \mathcal S'. \ }$$

---

**Summary.** The same sequence converges to `0` in `\mathcal D'` but diverges in `\mathcal S'`. The
contrast is structural: against compactly supported test functions the moving singularity eventually
leaves the support (location wins, limit `0`); against Schwartz test functions the unboundedly growing
order of differentiation can be detected at the receding base point (order wins, no limit). The function
`f = \sum (x-n)^n \chi(x-n)/n!` is the explicit witness — the `n`-th-derivative-equals-`1`-at-`n`
property is engineered by the monomial `(x-n)^n/n!`, while the `1/n!` enforces Schwartz decay. ∎

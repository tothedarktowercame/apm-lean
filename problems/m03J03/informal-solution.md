<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m03J03: Four distributions — Dirac comb, polynomial-growth Fourier series, derivatives of H·sin, and a non-example

## Why It's Hard

A "distribution" is not just *any* gadget that eats test functions and returns a
number. To be an element of `𝒟'(ℝ)` a functional `T` must be **(i) linear** and
**(ii) continuous**, where continuity means a *seminorm estimate*: for every
compact `K` there are `C, m` with `|T(φ)| ≤ C Σ_{j≤m} sup|φ^{(j)}|` for all `φ`
supported in `K`. Each of the four parts probes a different way this can succeed
or fail, so the difficulty is that there is no single computation — you need the
right tool for each.

- **(a)** is an *infinite* sum that you must argue is locally finite, then bound.
- **(b)** is a series whose coefficients *grow* polynomially; it converges only
  because test functions are infinitely smooth, and the smoothness must be
  converted into decay by integration by parts. This is the polynomial-growth ↔
  rapid-decay duality that makes Fourier series of distributions work at all.
- **(c)** is a trap: you must track *which* boundary terms produce Dirac masses
  and which vanish. The function `H·sin` is continuous at `0` (so `D` produces no
  delta), but its derivative `H·cos` is *not* (so `D²` does).
- **(d)** looks like a distribution and is even continuous, but fails the most
  basic axiom — linearity — and the whole point is to notice that.

## The Key Insight

Every part reduces to controlling `T(φ)` by finitely many derivative-seminorms of
`φ` — and the absolute value `|·|` in part (d) is precisely what destroys the
*linear* structure those seminorms presuppose.

The load-bearing trick is **integration by parts against a test function**. In
(b) it turns `|a_n| ≤ A|n|^N` into a *summable* bound, because each integration
by parts pays a factor `1/|n|` and `φ` can be differentiated as many times as we
like: differentiate `N+2` times and `Σ |n|^{-2} < ∞` closes it. In (c) the *same*
integration by parts, but now watching the boundary term at `x=0`, is exactly the
bookkeeping that decides whether a `δ` appears: a boundary value of `sin` (which
is `0`) gives nothing, a boundary value of `cos` (which is `1`) gives `δ`. The
clean check is that `H·sin` is the causal fundamental solution of `D²+1`:
`(D²+1)(H\sin) = δ`.

## Complete Proof

Throughout, `𝒟(ℝ) = C_c^∞(ℝ)` is the space of smooth compactly supported test
functions, `⟨T,φ⟩ = T(φ)`, and `H` is the Heaviside function (`H=1` on `(0,∞)`,
`H=0` on `(−∞,0)`). Distributional derivative is defined by
`⟨DT, φ⟩ = −⟨T, φ'⟩`. A functional `T` belongs to `𝒟'(ℝ)` iff it is linear and
satisfies, for each compact `K`, a bound
`|⟨T,φ⟩| ≤ C_K Σ_{j≤m} \sup|φ^{(j)}|` for all `φ` with `supp φ ⊆ K`.

---

### (a)  `T(φ) = Σ_{n=0}^∞ φ(n)` is a distribution

**Well-defined and linear.** If `supp φ ⊆ K` with `K` compact, then `φ(n) = 0`
for all but finitely many nonnegative integers `n` (only those `n ∈ K` survive).
So the sum is finite, and `T(φ) = Σ_{n∈K∩ℤ_{≥0}} φ(n)`. Linearity is immediate
from linearity of evaluation.

**Continuity (order 0).** Let `K` be compact and let `p = #(K ∩ ℤ_{≥0}) < ∞` be
the number of nonnegative integers in `K`. For `supp φ ⊆ K`,

$$|T(φ)| = \Big|\sum_{n \in K\cap\mathbb{Z}_{\ge 0}} φ(n)\Big| \le p\,\sup_x |φ(x)|.$$

This is the seminorm bound with `m = 0`, `C_K = p`. Hence `T ∈ 𝒟'(ℝ)`; in fact
`T = Σ_{n=0}^∞ δ_n`, a locally finite sum of Dirac masses (a one-sided Dirac
comb), and it has order `0`. ∎

---

### (b)  `T = Σ_{n=0}^∞ a_n e^{inx}` converges in `𝒟'(ℝ)` when `|a_n| ≤ A|n|^N`

Each `e^{inx}` is a smooth, bounded function, hence a distribution via
`⟨e^{inx}, φ⟩ = ∫ e^{inx} φ(x)\,dx`. Let `S_M = Σ_{n=0}^M a_n e^{inx}` be the
partial sums. We show `⟨S_M, φ⟩` converges for every `φ ∈ 𝒟`, with a limit that
is a distribution; that is exactly convergence in `𝒟'(ℝ)`.

**Integration-by-parts decay.** Fix `φ ∈ 𝒟` and `n ≥ 1`. Since
`e^{inx} = \frac{1}{in}\frac{d}{dx} e^{inx}` and `φ` has compact support, repeated
integration by parts (the boundary terms vanish) gives, for any `k ≥ 0`,

$$\int e^{inx} φ(x)\,dx = \frac{(-1)^k}{(in)^k}\int e^{inx} φ^{(k)}(x)\,dx,
\qquad\text{so}\qquad
\Big|\int e^{inx} φ\,dx\Big| \le \frac{1}{|n|^{k}}\,\|φ^{(k)}\|_{L^1}.$$

**Absolute convergence.** Take `k = N+2`. Then for `n ≥ 1`,

$$|a_n|\,\Big|\int e^{inx} φ\,dx\Big|
\le A|n|^{N}\cdot \frac{\|φ^{(N+2)}\|_{L^1}}{|n|^{N+2}}
= A\,\|φ^{(N+2)}\|_{L^1}\,\frac{1}{n^{2}},$$

and `Σ_{n≥1} n^{-2} < ∞`. The `n=0` term is `a_0 ∫φ`, finite. Hence
`⟨S_M, φ⟩ → ⟨T, φ⟩ := Σ_{n=0}^∞ a_n ∫ e^{inx}φ\,dx` absolutely, for every `φ`.

**The limit is a distribution.** Summing the bound above, for `supp φ ⊆ K`
(say `K ⊆ [−R,R]`, so `‖ψ‖_{L^1} ≤ 2R\,‖ψ‖_∞`),

$$|⟨T,φ⟩| \le |a_0|\,\|φ\|_{L^1} + A\Big(\sum_{n\ge1}\tfrac1{n^2}\Big)\|φ^{(N+2)}\|_{L^1}
\le C_K\Big(\sup|φ| + \sup|φ^{(N+2)}|\Big).$$

This is the seminorm estimate with `m = N+2`. So `T ∈ 𝒟'(ℝ)`, of order `≤ N+2`,
and the series converges to it in `𝒟'`. ∎

---

### (c)  `D(H\sin)` and `D^2(H\sin)`

Write `g(x) = H(x)\sin x` (equal to `\sin x` for `x>0`, and `0` for `x<0`). Note
`g` is **continuous** at `0` because `\sin 0 = 0`.

**Claim.** `D(H\sin) = H(x)\cos x` and `D^2(H\sin) = δ - H(x)\sin x`.

**Heuristic (Leibniz with `H' = δ`).**
`D(H\sin) = H'\sin + H\cos = (\sin 0)\,δ + H\cos = H\cos`, since the delta is
weighted by `\sin 0 = 0`. Then
`D^2(H\sin) = D(H\cos) = H'\cos + H(\cos)' = (\cos 0)\,δ - H\sin = δ - H\sin`,
since now the delta is weighted by `\cos 0 = 1`.

**Verification from the definition.** For the first derivative and any `φ ∈ 𝒟`,

$$⟨D(H\sin), φ⟩ = -⟨H\sin, φ'⟩ = -\int_0^\infty \sin x\,φ'(x)\,dx
= -\Big([\sin x\,φ(x)]_0^\infty - \int_0^\infty \cos x\,φ(x)\,dx\Big).$$

The boundary term vanishes (`φ(∞)=0` by compact support, and `\sin 0 = 0`), so
this equals `∫_0^∞ \cos x\,φ\,dx = ⟨H\cos, φ⟩`. Thus `D(H\sin) = H\cos`. ✓

For the second derivative,

$$⟨D^2(H\sin), φ⟩ = ⟨H\sin, φ''⟩ = \int_0^\infty \sin x\,φ''(x)\,dx.$$

Integrate by parts once: `= [\sin x\,φ']_0^\infty - ∫_0^∞ \cos x\,φ'\,dx
= -∫_0^∞ \cos x\,φ'\,dx` (boundary term `0`, as `\sin 0 = 0`). Integrate again:

$$-\int_0^\infty \cos x\,φ'\,dx
= -\Big([\cos x\,φ]_0^\infty - \int_0^\infty(-\sin x)φ\,dx\Big)
= -\big(-φ(0)\big) - \int_0^\infty \sin x\,φ\,dx = φ(0) - ⟨H\sin, φ⟩.$$

Here the boundary term contributes `-\cos 0\,φ(0) = -φ(0)` at the lower limit.
Hence `⟨D^2(H\sin),φ⟩ = ⟨δ,φ⟩ - ⟨H\sin,φ⟩`, i.e. `D^2(H\sin) = δ - H\sin`. ✓

**Consistency check.** Combining, `(D^2 + 1)(H\sin) = δ`: `H(x)\sin x` is the
causal fundamental solution of the operator `D^2 + 1`, as expected. ∎

---

### (d)  `T(φ) = |φ(0)|` is **not** a distribution

A distribution must be **linear**. The functional `T(φ) = |φ(0)|` is not, and a
single explicit pair of test functions exhibits the failure.

- *Homogeneity fails for negative scalars.* For any `φ` with `φ(0) ≠ 0`,
  `T(-φ) = |-φ(0)| = |φ(0)| = T(φ) ≠ -T(φ)`.
- *Additivity fails.* Choose `φ, ψ ∈ 𝒟` with `φ(0) = 1` and `ψ(0) = -1` (e.g. a
  bump `χ` with `χ(0)=1`, and `φ = χ`, `ψ = -χ`). Then

$$T(φ + ψ) = |φ(0) + ψ(0)| = |0| = 0,
\quad\text{but}\quad T(φ) + T(ψ) = 1 + 1 = 2.$$

Since `T(φ+ψ) ≠ T(φ) + T(ψ)`, `T` is not linear. (It is continuous and even
positively homogeneous — but linearity is part of the *definition* of `𝒟'(ℝ)`,
and it is exactly the property the absolute value destroys.) Therefore `T` does
not define an element of `𝒟'(ℝ)`. ∎

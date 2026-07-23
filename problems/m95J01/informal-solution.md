<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95J01: A finite-dimensional Hilbert space of decaying polynomials, and differentiation as I + nilpotent

## Why It's Hard

The space `H = \{e^{-x}\sum_{k=0}^n a_k x^k\}` is presented as a space of *functions* on `[0,\infty)`
with an integral inner product, which makes it look infinite-dimensional and analytic. The first and
most important realization is that it is nothing of the sort: it is just `e^{-x}` times the
`(n+1)`-dimensional space of polynomials of degree `\le n`, so **everything reduces to finite-dimensional
linear algebra** once you peel off the `e^{-x}`. The difficulty is psychological as much as technical —
resisting the urge to do hard analysis when the right move is to recognize a disguised copy of `P_n`.

The subtler points are operator-theoretic. The second-derivative operator `T = (d/dx)^2` does not look
like it should preserve `H`, but conjugating by `e^{-x}` turns it into the polynomial operator `(D-I)^2`,
which is `I` plus a **nilpotent** — explaining at once why `T` is triangular with a single eigenvalue,
why `T-I` is not invertible, and exactly which `g` lie in the range of `T-I`. And the orthonormal basis
hides a classical object: the `e^{-x}` weight is the Laguerre weight after a rescaling `u = 2x`.

## The Key Insight

**Peel off the exponential.** The map `P \mapsto e^{-x}P` is a linear isomorphism from `P_n` (polynomials
of degree `\le n`) onto `H`, so `\dim H = n+1` and `\{e^{-x}x^k\}_{k=0}^n` is a basis. Under this
isomorphism, differentiation conjugates to a shift: since `(e^{-x}P)' = e^{-x}(P' - P) = e^{-x}(D-I)P`,

$$T = \Big(\tfrac{d}{dx}\Big)^2 \ \longleftrightarrow\ (D - I)^2 = D^2 - 2D + I \quad \text{acting on } P_n.$$

Because `D` is nilpotent on `P_n` (`D^{n+1} = 0`), `T = I + (\text{nilpotent})`: triangular, sole
eigenvalue `1`. Consequently `T - I \leftrightarrow D^2 - 2D = D(D-2)`, whose range on `P_n` is exactly
the polynomials of degree `\le n-1` — giving the solvability criterion. Finally the inner product
`\int_0^\infty e^{-2x}PQ\,dx` becomes, under `u = 2x`, the **Laguerre** inner product
`\tfrac12\int_0^\infty e^{-u}P(\tfrac u2)Q(\tfrac u2)\,du`, so the orthonormal basis is
`\sqrt2\,e^{-x}L_m(2x)`.

## Complete Proof

Write `e_k(x) = e^{-x}x^k`. Throughout we use the Gamma integral
`\int_0^\infty x^m e^{-2x}\,dx = \dfrac{m!}{2^{m+1}}`.

### (a) `H` is a Hilbert space of dimension `n+1`

The map `\Phi : P_n \to H`, `\Phi(P) = e^{-x}P`, is linear, and injective (`e^{-x}P \equiv 0 \Rightarrow P \equiv 0`
since `e^{-x} \ne 0`), with image `H` by definition. So `H \cong P_n` and `\dim H = n+1`; the functions
`\{e_k\}_{k=0}^n` are a basis (the `x^k` are independent and `e^{-x} \ne 0`).

The form `\langle f,g\rangle = \int_0^\infty fg\,dx` is finite on `H`: for `f,g \in H`, `fg = e^{-2x}\cdot(\text{poly})`
and `\int_0^\infty e^{-2x}x^m\,dx < \infty`. It is bilinear, symmetric, and positive definite
(`\langle f,f\rangle = \int_0^\infty f^2 \ge 0`, `= 0` only if `f \equiv 0` by continuity), hence an inner
product. A finite-dimensional inner-product space is automatically complete, so `H` is a **Hilbert space**
of dimension `n+1`. ∎

### (b) `T = (d/dx)^2` maps `H \to H`; its matrix

For `f = e^{-x}P` with `P \in P_n`, differentiating twice,

$$f' = e^{-x}(P' - P), \qquad f'' = e^{-x}\big(P'' - 2P' + P\big) = e^{-x}(D-I)^2 P,$$

and `(D-I)^2 P = P'' - 2P' + P \in P_n`. So `Tf = e^{-x}(D-I)^2P \in H`: `T` maps `H` into `H`, and it is
linear (differentiation is). **In the basis `\{e_k\}`:** with `P = x^k`,

$$T e_k = e^{-x}\big(x^k - 2k\,x^{k-1} + k(k-1)\,x^{k-2}\big) = e_k - 2k\,e_{k-1} + k(k-1)\,e_{k-2}$$

(with `e_{-1} = e_{-2} = 0`). Thus the matrix of `T` is **lower triangular** with every diagonal entry
`1`, subdiagonal entries `-2k`, and sub-subdiagonal entries `k(k-1)`:

$$T = I + N, \qquad N \text{ strictly lower triangular (nilpotent)}.$$

Equivalently, `T` is conjugate (via `\Phi`) to `(D-I)^2` on `P_n`. Its only eigenvalue is `1`, with
algebraic multiplicity `n+1`. ∎

### (c) Solvability of `(T-I)f = g`

Conjugating, `T - I \leftrightarrow (D-I)^2 - I = D^2 - 2D = D(D-2)` on `P_n`. So with `f = e^{-x}P`,
`g = e^{-x}Q`, the equation `(T-I)f = g` is

$$P'' - 2P' = Q, \qquad\text{i.e.}\qquad S P = Q, \quad S := D(D-2).$$

Compute `S` on monomials: `S(x^k) = k(k-1)x^{k-2} - 2k\,x^{k-1}`, with leading term `-2k\,x^{k-1}` for
`k \ge 1`, and `S(1) = 0`. Hence:

- `\ker S = \{P : P'' = 2P'\} = \{\text{constants}\}` (a nonzero polynomial `P'` cannot equal `2P'` unless
  `P' = 0`), `\dim \ker S = 1`;
- the images `S(x), S(x^2), \dots, S(x^n)` have distinct degrees `0, 1, \dots, n-1`, so they are
  independent and span `P_{n-1}`; thus `\operatorname{range} S = P_{n-1}` (dimension `n`, consistent with
  rank–nullity `(n+1) - 1 = n`).

Therefore `SP = Q` is solvable in `P_n` **iff** `Q \in P_{n-1}`, i.e. `Q` has degree `\le n-1`. Translating
back: writing `g(x) = e^{-x}\sum_{k=0}^n b_k x^k`, the equation `(T-I)f = g` has a solution `f \in H`

$$\boxed{\ \text{if and only if } b_n = 0,\ }$$

i.e. iff `g` lies in `\operatorname{span}\{e^{-x}x^k : 0 \le k \le n-1\}` — the coefficient of `x^n` in
`e^x g(x)` vanishes. (When solvable, the solution is unique up to adding a constant multiple of `e_0 = e^{-x}`,
the kernel of `T-I`.) ∎

### (d) Constructing an orthonormal basis

**General method — Gram–Schmidt.** Apply the Gram–Schmidt process to the basis `\{e_k = e^{-x}x^k\}_{k=0}^n`
using `\langle e_j, e_k\rangle = \int_0^\infty e^{-2x}x^{j+k}\,dx = \dfrac{(j+k)!}{2^{j+k+1}}`. This
produces an orthonormal basis `\{\varphi_0, \dots, \varphi_n\}` with `\varphi_m` a fixed linear
combination of `e_0, \dots, e_m`.

**Explicit answer — Laguerre.** The Gram–Schmidt output is a classical family. For `f = e^{-x}P`,
`g = e^{-x}Q`, substitute `u = 2x`:

$$\langle f, g\rangle = \int_0^\infty e^{-2x}P(x)Q(x)\,dx = \frac12\int_0^\infty e^{-u}\,P\!\big(\tfrac u2\big)Q\!\big(\tfrac u2\big)\,du,$$

which is (half) the **Laguerre** inner product with weight `e^{-u}` on `[0,\infty)`. Since the Laguerre
polynomials satisfy `\int_0^\infty e^{-u}L_j(u)L_k(u)\,du = \delta_{jk}`, taking `P(x) = L_m(2x)` gives

$$\big\langle e^{-x}L_j(2x),\, e^{-x}L_k(2x)\big\rangle = \frac12\int_0^\infty e^{-u}L_j(u)L_k(u)\,du = \frac12\,\delta_{jk}.$$

Hence

$$\boxed{\ \varphi_m(x) = \sqrt{2}\;e^{-x} L_m(2x), \qquad m = 0, 1, \dots, n,\ }$$

is an orthonormal basis of `H` (each `L_m(2x)` is a degree-`m` polynomial, so `\varphi_m \in H`, and the
`n+1` of them are independent). This is exactly what Gram–Schmidt on `\{e^{-x}x^k\}` produces, in closed
form. ∎

**Remark.** The whole problem is `P_n` wearing an `e^{-x}` coat: dimension `n+1` (a), differentiation
`= (D-I)^2 = I + \text{nilpotent}` (b), `T-I = D(D-2)` with range the degree-`\le n-1` polynomials (c),
and the `e^{-2x}` integral `=` rescaled Laguerre weight (d). Recognizing the disguise turns four analysis
questions into four short linear-algebra computations.

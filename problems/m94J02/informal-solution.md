<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94J02: A weighted ℓ¹ algebra of power series, and a diagonal dilation operator

## Why It's Hard

The space `X` is defined by a power-series representation, but every part becomes transparent only
after you make the right identification: `X` is the **weighted `\ell^1` space** of coefficient
sequences, `f \leftrightarrow (f_n)` with norm `\|f\| = \sum_n |f_n| w_n`, `w_n = n^2+1`. Once you
see this, the six parts are really six facts about weighted `\ell^1`: completeness, an embedding
into `\ell^1` (continuity), submultiplicativity of the weight (Banach algebra), Fekete's subadditive
lemma (the `\|f^n\|^{1/n}` limit), and a *diagonal* operator (compactness and spectrum).

The genuinely subtle point is the algebra structure. Pointwise multiplication of power series is
**convolution** (the Cauchy product) of coefficients, and `\|fg\| \le \|f\|\,\|g\|` requires the
weight to be *submultiplicative*: `w_{j+k} \le w_j w_k`. The weight `n^2+1` *almost* satisfies this
but fails at exactly one place — `w_2 = 5 > 4 = w_1^2` — so the literal inequality in part (c) is
false (take `f=g=z`). The honest statement is `\|fg\| \le \tfrac54\|f\|\,\|g\|`, which still makes
`X` a Banach algebra; the constant `1` is recovered only with the equivalent submultiplicative weight
`(n+1)^2`. Recognizing this is the crux.

## The Key Insight

**Pass to coefficients.** Under `f \leftrightarrow (f_n)`:

- `X \cong \ell^1(w)`, `w_n = n^2+1` — a weighted `\ell^1`, hence complete **(a)**.
- `\sum|f_n| \le \sum |f_n| w_n = \|f\|`, so the series converges *uniformly* on `D` — functions are
  continuous **(b)**.
- multiplication `=` Cauchy product, and `w_{j+k} \le \tfrac54 w_j w_k` gives
  `\|fg\| \le \tfrac54\|f\|\|g\|` **(c)**.
- submultiplicativity (up to a constant) `\Rightarrow` `\log\|f^n\|` is subadditive `\Rightarrow`
  Fekete gives `\|f^n\|^{1/n} \to r(f)` **(d)**.
- the dilation `(Tf)(z) = f(z/2)` multiplies the `n`-th coefficient by `2^{-n}`: it is a **diagonal
  operator** with entries `2^{-n} \to 0`, hence a norm-limit of finite-rank truncations — **compact (e)** —
  with spectrum the closure of its eigenvalues `\{2^{-n}\} \cup \{0\}` **(f)**.

Everything reduces to the one move of reading `f` through its coefficient sequence.

## Complete Proof

Identify `f(z) = \sum_{n\ge0} f_n z^n` with `(f_n)_{n\ge0}` and write `w_n = n^2 + 1 \ge 1`, so
`\|f\| = \sum_n |f_n| w_n`. Distinct power series have distinct coefficients, so `\|f\| = 0 \Rightarrow f \equiv 0`;
the norm axioms are immediate. Thus `X` is (isometrically) the weighted space `\ell^1(w)`.

### (a) `X` is a Banach space

Only completeness needs proof. Let `(f^{(k)})_k` be Cauchy in `X`. Since `w_n \ge 1`,
`|f_n^{(k)} - f_n^{(j)}| \le |f_n^{(k)} - f_n^{(j)}| w_n \le \|f^{(k)} - f^{(j)}\|`, so for each fixed `n`
the scalars `(f_n^{(k)})_k` are Cauchy in `\mathbb C`; let `f_n = \lim_k f_n^{(k)}`. Given `\varepsilon>0`,
pick `N` with `\|f^{(k)} - f^{(j)}\| < \varepsilon` for `k,j \ge N`. For any finite `M`,
`\sum_{n\le M} |f_n^{(k)} - f_n^{(j)}| w_n < \varepsilon`; letting `j \to \infty` then `M \to \infty`,

$$\sum_{n} |f_n^{(k)} - f_n|\, w_n \le \varepsilon \qquad (k \ge N).$$

Hence `f^{(k)} - f \in X` with `\|f^{(k)} - f\| \le \varepsilon`, and `f = f^{(N)} - (f^{(N)} - f) \in X`.
So `f^{(k)} \to f` in `X`, and `X` is complete. ∎

### (b) Every `f \in X` is continuous on `D`

Since `w_n \ge 1`, `\sum_n |f_n| \le \sum_n |f_n| w_n = \|f\| < \infty`. For `|z| \le 1`,
`|f_n z^n| \le |f_n|`, so by the Weierstrass `M`-test the series `\sum f_n z^n` converges **uniformly**
on `D`. A uniform limit of the (continuous) partial-sum polynomials is continuous, so `f \in C(D)`.
(Indeed `f` is holomorphic in the interior and continuous up to the boundary.) ∎

### (c) `X` is a Banach algebra

The product `fg` has coefficients given by the Cauchy product `(fg)_n = \sum_{k=0}^n f_k g_{n-k}`, so

$$\|fg\| = \sum_n \Big|\sum_{k=0}^n f_k g_{n-k}\Big| w_n \le \sum_n \sum_{k=0}^n |f_k|\,|g_{n-k}|\, w_n.$$

**Weight estimate.** For `j,k \ge 0`,
`w_j w_k - w_{j+k} = (1+j^2)(1+k^2) - (1+(j+k)^2) = j^2k^2 - 2jk = jk(jk-2)`, which is `\ge 0` unless
`jk = 1`, i.e. `j = k = 1`. So `w_{j+k} \le w_j w_k` for all `(j,k) \ne (1,1)`, while at `(1,1)`,
`w_2 = 5 = \tfrac54 \cdot 4 = \tfrac54 w_1^2`. Checking the ratio `w_{j+k}/(w_j w_k)` elsewhere (it is
`\le 1`), the maximum is `\tfrac54`, attained at `(1,1)`. Hence

$$w_{j+k} \le \tfrac54\, w_j w_k \qquad \text{for all } j,k \ge 0.$$

Therefore, with `n = k + (n-k)`,

$$\|fg\| \le \tfrac54 \sum_n \sum_{k} |f_k| w_k\, |g_{n-k}| w_{n-k}
= \tfrac54 \Big(\sum_k |f_k| w_k\Big)\Big(\sum_m |g_m| w_m\Big) = \tfrac54\,\|f\|\,\|g\|.$$

Multiplication is thus continuous, and `X` (complete by (a)) is a **Banach algebra**.

> **Honest caveat.** The *literal* inequality `\|fg\| \le \|f\|\|g\|` of the problem statement is
> **false** for this weight: with `f = g = z`, `\|z^2\| = w_2 = 5` while `\|z\|^2 = w_1^2 = 4`, so
> `\|z^2\| > \|z\|^2`. The failure is by exactly the factor `\tfrac54` and comes solely from the single
> weight relation `w_2 > w_1^2`. The submultiplicative inequality with constant `1` is restored by the
> equivalent norm with weight `(n+1)^2`, which satisfies `((j+k)+1)^2 \le ((j+1)(k+1))^2`; we use the
> faithful constant `\tfrac54` below, which changes nothing in parts (d)–(f).

### (d) `\|f^n\|^{1/n}` converges

By (c), `\|f^{m+n}\| \le \tfrac54 \|f^m\|\,\|f^n\|`. For `f \ne 0`, no power vanishes (`f^n \equiv 0`
would force `f \equiv 0`), so `\|f^n\| > 0` and we may set `c_n = \log\|f^n\| + \log\tfrac54`. Then

$$c_{m+n} = \log\|f^{m+n}\| + \log\tfrac54 \le \big(\log\tfrac54 + \log\|f^m\| + \log\|f^n\|\big) + \log\tfrac54 = c_m + c_n,$$

so `(c_n)` is **subadditive**. By **Fekete's lemma**, `c_n/n \to \inf_n c_n/n =: L \in [-\infty, \infty)`.
Since `\log\tfrac54 / n \to 0`,

$$\frac1n \log\|f^n\| = \frac{c_n}{n} - \frac{\log\tfrac54}{n} \longrightarrow L,
\qquad\text{hence}\qquad \|f^n\|^{1/n} \to e^L.$$

(If `f_0 = f(0) \ne 0` then `\|f^n\| \ge |f_0|^n` keeps `L` finite; if `f_0 = 0` the limit may be `0`.)
The limit `e^L = r(f)` is the **spectral radius** of `f` in `X` (Gelfand's formula). ∎

### (e) `T`, `(Tf)(z) = f(z/2)`, is compact

In coefficients, `(Tf)(z) = \sum_n f_n (z/2)^n = \sum_n 2^{-n} f_n z^n`, so `T` is the **diagonal
operator** `(Tf)_n = 2^{-n} f_n`. It is bounded: `\|Tf\| = \sum_n 2^{-n} |f_n| w_n \le \|f\|`. Let
`T_N` keep only coefficients `n \le N` (zeroing the rest); each `T_N` has finite-dimensional range
`\subseteq \operatorname{span}\{1, z, \dots, z^N\}`. Then

$$\|(T - T_N) f\| = \sum_{n > N} 2^{-n} |f_n| w_n \le 2^{-(N+1)} \sum_{n>N} |f_n| w_n \le 2^{-(N+1)}\|f\|,$$

so `\|T - T_N\| \le 2^{-(N+1)} \to 0`. `T` is a norm-limit of finite-rank operators, hence **compact**. ∎

### (f) The spectrum of `T`

`T` is diagonal with `T z^n = 2^{-n} z^n`, so each `2^{-n}` (`n = 0,1,2,\dots`) is an **eigenvalue** with
eigenvector `z^n`. Thus the point spectrum contains `\{2^{-n} : n \ge 0\} = \{1, \tfrac12, \tfrac14, \dots\}`.

For `\lambda \notin \{2^{-n}\} \cup \{0\}`: since `2^{-n} \to 0`, the set `\{2^{-n}\} \cup \{0\}` is
closed, so `d := \inf_n |2^{-n} - \lambda| > 0`. The diagonal operator `(T-\lambda I)^{-1}`, multiplying
the `n`-th coefficient by `(2^{-n} - \lambda)^{-1}` (each `\le 1/d`), is bounded:
`\|(T-\lambda I)^{-1} g\| \le \tfrac1d \|g\|`. So `\lambda` is in the resolvent set.

Finally `0 \in \sigma(T)`: `T` is injective (`Tf = 0 \Rightarrow 2^{-n} f_n = 0 \,\forall n \Rightarrow f = 0`),
so `0` is *not* an eigenvalue, but `T` is not surjective — e.g. `g_n = 2^{-n}/w_n` lies in `X` while its
only preimage has `f_n = 1/w_n \cdot ... = 1`, giving `\sum w_n = \infty \notin X` — so `0` belongs to the
spectrum (consistent with `T` compact: `0` is the accumulation point of the eigenvalues `2^{-n} \to 0`).
Therefore

$$\boxed{\ \sigma(T) = \{0\} \cup \{2^{-n} : n = 0, 1, 2, \dots\} = \{0, 1, \tfrac12, \tfrac14, \tfrac18, \dots\}.\ }$$

The eigenvalues are exactly the `2^{-n}` (point spectrum); `0` lies in the spectrum but is not an
eigenvalue (it sits in the continuous spectrum, `T` being injective with dense range). ∎

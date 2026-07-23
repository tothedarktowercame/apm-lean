<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99A03: Normal nilpotents are zero, but non-normal nilpotents hide non-compact lower powers

## Why It's Hard

The two parts are a matched pair that together pinpoint the role of **normality**. Part (a) says a compact
normal operator with `A^3 = 0` must vanish — nilpotency is fatal for normal operators. Part (b) asks you to
*violate* the analogue without normality: build `A` with `A^3` compact (indeed `A^3 = 0`) while `A` and
`A^2` are **not** compact. The difficulty is appreciating that these are not in tension: the property that
makes (a) work — that a normal operator is determined by its eigenvalues, which a power sends to zero — is
exactly the property part (b) must abandon.

For (a) the trap is to overcomplicate; the spectral theorem for compact normal operators reduces everything
to scalars `\lambda_n^3 = 0 \Rightarrow \lambda_n = 0`. For (b) the challenge is constructive: you need an
operator that is genuinely "large" (non-compact) at powers `1` and `2` but collapses at power `3`. The clean
device is a **nilpotent block shift** carrying three copies of an infinite-dimensional identity — the
identity blocks keep `A` and `A^2` non-compact, while the shift structure forces `A^3 = 0`.

## The Key Insight

- **(a)** A compact normal operator diagonalizes: `A = \sum_n \lambda_n \langle \cdot, e_n\rangle e_n` with
  orthonormal `\{e_n\}` and eigenvalues `\lambda_n \to 0`. Then `A^3 = \sum_n \lambda_n^3 \langle \cdot, e_n\rangle e_n = 0`
  forces every `\lambda_n^3 = 0`, hence every `\lambda_n = 0`, hence `A = 0`. (Normal operators cannot be
  nonzero nilpotents — equivalently `\|A\| = r(A) = \lim\|A^n\|^{1/n} = 0`.)
- **(b)** On `H = K \oplus K \oplus K` with `K` infinite-dimensional, the shift `A(x,y,z) = (y,z,0)` satisfies
  `A^2(x,y,z) = (z,0,0)`, `A^3 = 0`. The "`I`-blocks" make `A` and `A^2` non-compact (they map an orthonormal
  sequence to a `\sqrt2`-separated one), while `A^3 = 0` is trivially compact. This `A` is **not normal** —
  which is exactly why it can be a nonzero nilpotent, in contrast to (a).

## Complete Proof

### (a) Compact + normal + `A^3 = 0` `\Rightarrow` `A = 0`

Since `A` is compact and normal, the **spectral theorem for compact normal operators** applies: there is an
orthonormal system `\{e_n\}` and scalars `\lambda_n` (the eigenvalues, with `\lambda_n \to 0` if infinitely
many) such that

$$Ax = \sum_n \lambda_n \langle x, e_n\rangle e_n \qquad (x \in H), \qquad A e_n = \lambda_n e_n.$$

Powers act by raising the eigenvalues: `A^3 x = \sum_n \lambda_n^3 \langle x, e_n\rangle e_n`. The hypothesis
`A^3 = 0` gives, applying to `x = e_m`, `\lambda_m^3 e_m = 0`, so `\lambda_m^3 = 0`, hence `\lambda_m = 0` for
every `m`. Therefore `Ax = \sum_n 0 \cdot \langle x, e_n\rangle e_n = 0` for all `x`, i.e.

$$\boxed{\ A = 0.\ }$$

*Alternative (normality alone).* For a normal operator `\|A^2\| = \|A\|^2`, so by induction
`\|A^{2^k}\| = \|A\|^{2^k}` and the spectral radius is `r(A) = \lim_k \|A^{2^k}\|^{1/2^k} = \|A\|`. But
`A^3 = 0 \Rightarrow A^4 = 0`, so `\|A^{2^k}\| = 0` once `2^k \ge 4`, giving `r(A) = 0` and `\|A\| = 0`. Either
way `A = 0`. (Compactness is convenient but the spectral-radius argument needs only normality.) ∎

### (b) An operator with `A, A^2` non-compact but `A^3` compact

Let `K` be an infinite-dimensional Hilbert space (e.g. `K = \ell^2`) and set `H = K \oplus K \oplus K`.
Define `A : H \to H` by

$$A(x, y, z) = (y, z, 0),$$

a `3`-step nilpotent "block shift" (matrix form `\begin{psmallmatrix} 0 & I & 0 \\ 0 & 0 & I \\ 0 & 0 & 0\end{psmallmatrix}`).

**`A` is bounded.** `\|A(x,y,z)\|^2 = \|y\|^2 + \|z\|^2 \le \|x\|^2 + \|y\|^2 + \|z\|^2 = \|(x,y,z)\|^2`, so
`\|A\| \le 1`; linearity is clear.

**Powers.** `A^2(x,y,z) = A(y,z,0) = (z,0,0)` and `A^3(x,y,z) = A(z,0,0) = (0,0,0)`, so

$$A^3 = 0,$$

which is compact (the zero operator).

**`A` is not compact.** Let `\{e_n\}` be orthonormal in `K` and put `w_n = (0, e_n, 0) \in H`, so
`\|w_n\| = 1`. Then `A w_n = (e_n, 0, 0)`, and for `n \ne m`,
`\|A w_n - A w_m\| = \|e_n - e_m\| = \sqrt2`. The bounded sequence `(w_n)` has image with no Cauchy (hence
no convergent) subsequence, so `A` is not compact.

**`A^2` is not compact.** Put `u_n = (0,0,e_n)`, `\|u_n\| = 1`. Then `A^2 u_n = (e_n, 0, 0)`, again
`\sqrt2`-separated, so `(A^2 u_n)` has no convergent subsequence: `A^2` is not compact.

Thus `A` and `A^2` are **not** compact, while `A^3 = 0` **is** compact. ∎

**Remark.** The two parts are exactly complementary. In (a), normality means `A` is unitarily a
multiplication by its eigenvalues, so a vanishing power kills every eigenvalue and `A = 0` — a normal
nilpotent must be zero. The operator in (b) is the prototypical **non-normal** nilpotent: a strict block
shift (`A^*A \ne AA^*`), and its non-normality is precisely what lets `A^3 = 0` coexist with non-compact
`A, A^2`. The identity blocks `I` riding inside `A` and `A^2` keep those powers as "large" as the
infinite-dimensional identity, and only the third composition lines them up to annihilate. The moral:
compactness of a high power says nothing about lower powers unless extra structure (like normality) ties
the powers to a common eigenbasis.

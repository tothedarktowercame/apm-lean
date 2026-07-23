<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94A02: Real parts of eigenvalues are trapped by the symmetric part (Bendixson)

## Why It's Hard

You are comparing two genuinely different spectra. The matrix `A` is a general real matrix, so
its eigenvalues `\lambda` are typically **complex** and its eigenvectors live in `\mathbb{C}^n`.
The matrix `B = (A+A^t)/2` is real *symmetric*, so its eigenvalues `\sigma_i` are **real** and
it has a real orthonormal eigenbasis. The claim `\sigma_n \le \Re(\lambda) \le \sigma_1` relates
the *real part* of a complex number attached to `A` to the *real* extreme eigenvalues of a
different matrix `B`. There is no eigenvector shared between `A` and `B`, so you cannot just
compare characteristic polynomials; you need a bridge.

The temptation is to work with real quadratic forms, but the eigenvector of `A` is complex, so
one must be careful to use the Hermitian (conjugate) inner product `x^* \cdot x`, and to see why
the *antisymmetric* part of `A` contributes nothing to the real part. Missing the complex
conjugation is the standard error.

## The Key Insight

Test the eigenvalue equation against its own eigenvector with the **Hermitian** form. If
`Ax = \lambda x` with `x \in \mathbb{C}^n`, `\|x\| = 1`, then `x^* A x = \lambda`. Taking real
parts and using that `A` is real (so `A^* = A^t`),

$$\Re(\lambda) = \tfrac12\big(x^* A x + \overline{x^* A x}\big)
= \tfrac12\big(x^* A x + x^* A^t x\big) = x^*\Big(\frac{A+A^t}{2}\Big)x = x^* B x.$$

So **the real part of every eigenvalue of `A` is a Rayleigh quotient of the symmetric part `B`**.
Because `B` is Hermitian (real symmetric), its Rayleigh quotients on unit vectors are exactly
the interval `[\sigma_n, \sigma_1]` — the Rayleigh–Ritz / min–max bound. That instantly gives
`\sigma_n \le \Re(\lambda) \le \sigma_1`. The antisymmetric part `(A-A^t)/2` drops out precisely
because its quadratic form is purely imaginary, contributing only to `\Im(\lambda)`.

## Complete Proof

**Setup.** Let `\lambda \in \mathbb{C}` be an eigenvalue of `A` with eigenvector `x\in\mathbb{C}^n`,
normalized so `x^* x = \|x\|^2 = 1` (here `x^*` is the conjugate transpose). Let
`B = (A+A^t)/2`. Since `A` is real, `B` is real and symmetric, hence Hermitian with real
eigenvalues `\sigma_1 \ge \cdots \ge \sigma_n` and a real orthonormal eigenbasis.

**Step 1 — The real part is a Rayleigh quotient of `B`.** From `Ax = \lambda x` and `x^*x=1`,

$$x^* A x = x^*(\lambda x) = \lambda\, (x^* x) = \lambda.$$

Now `x^* A x` is a scalar, so it equals its own transpose, and its complex conjugate is

$$\overline{x^* A x} = (x^* A x)^* = x^* A^* x = x^* A^t x,$$

using `A^* = \overline{A}^t = A^t` because `A` is real. Therefore

$$\Re(\lambda) = \frac{x^* A x + \overline{x^* A x}}{2}
= \frac{x^* A x + x^* A^t x}{2} = x^*\Big(\frac{A + A^t}{2}\Big) x = x^* B x. \tag{1}$$

(Consistently, the imaginary part comes from the antisymmetric part `C = (A-A^t)/2`:
`x^* C x` is purely imaginary since `\overline{x^*Cx} = x^* C^t x = -x^* C x`, so
`\Im(\lambda)` is carried entirely by `C` and `\Re(\lambda)` entirely by `B`.)

**Step 2 — Bounding a Hermitian Rayleigh quotient.** Because `B` is Hermitian, diagonalize
`B = Q\,\mathrm{diag}(\sigma_1,\dots,\sigma_n)\,Q^*` with `Q` unitary (indeed real orthogonal).
Put `y = Q^* x`, so `y^* y = x^* x = 1`. Then

$$x^* B x = y^*\,\mathrm{diag}(\sigma_i)\,y = \sum_{i=1}^n \sigma_i\,|y_i|^2,
\qquad \sum_{i=1}^n |y_i|^2 = 1.$$

This is a convex combination of the real numbers `\sigma_1,\dots,\sigma_n`, so it lies between
the smallest and the largest:

$$\sigma_n = \sigma_n\sum_i |y_i|^2 \le \sum_i \sigma_i |y_i|^2 \le \sigma_1 \sum_i |y_i|^2 = \sigma_1.
\tag{2}$$

In particular `x^* B x` is real, consistent with (1).

**Step 3 — Conclusion.** Combining (1) and (2),

$$\boxed{\ \sigma_n \le \Re(\lambda) \le \sigma_1\ }$$

for every eigenvalue `\lambda` of `A`. ∎

**The skew-symmetric case `A^t = -A`.** Then

$$B = \frac{A + A^t}{2} = \frac{A - A}{2} = 0,$$

so every eigenvalue of `B` is `0`: `\sigma_1 = \sigma_n = 0`. The bound forces
`0 \le \Re(\lambda) \le 0`, i.e.

$$\boxed{\ \Re(\lambda) = 0\ \text{for every eigenvalue }\lambda\text{ of }A.\ }$$

**Conclusion:** the eigenvalues of a real skew-symmetric matrix are **purely imaginary** (they
lie on the imaginary axis). Consequently they occur in conjugate pairs `\pm i\beta`, and for odd
`n` at least one eigenvalue is `0` — recovering the familiar spectral picture of an
infinitesimal rotation. ∎

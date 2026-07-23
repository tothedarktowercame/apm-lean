<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m94J03: The resolvent of a compact Hermitian operator is bounded by the reciprocal distance to the spectrum

## Why It's Hard

The inequality `\|R_z(A)\| \le \operatorname{dist}(z, \sigma(A))^{-1}` equates an *analytic* object —
the operator norm of `(z-A)^{-1}`, which measures worst-case amplification — with a purely
*geometric* one, the distance from `z` to the spectrum. For a **general** bounded operator this is
false: non-normal operators can have resolvents that are enormous even when `z` is far from the
spectrum (this is the entire subject of pseudospectra). So the result is *special*, and the proof
must use a structural feature that general operators lack.

The temptation is to manipulate `(z-A)^{-1}` abstractly, but that hides where the hypothesis enters.
The hypothesis "compact and Hermitian" is doing real work: it provides an honest **orthonormal
eigenbasis** with **real** eigenvalues, in which `A`, and therefore its resolvent, is literally
*diagonal*. The whole difficulty is recognizing that one should diagonalize and then read the norm
off the diagonal — and handling the kernel / the spectral point `0` correctly.

## The Key Insight

By the spectral theorem for compact self-adjoint operators, `H` has an orthonormal system of
eigenvectors `\{e_k\}` with **real** eigenvalues `\lambda_k`, and `A` acts diagonally:
`Ax = \sum_k \lambda_k \langle x, e_k\rangle e_k`, with the orthogonal complement of the
eigenvectors being `\ker A` (eigenvalue `0`). Then `z - A` is diagonal too, with entries `z - \lambda_k`
(and `z` on `\ker A`), so its inverse is diagonal with entries `(z - \lambda_k)^{-1}`:

$$R_z x = \frac{1}{z}\,x_0 + \sum_k \frac{1}{z - \lambda_k}\,\langle x, e_k\rangle\, e_k,
\qquad x = x_0 + \sum_k \langle x, e_k\rangle e_k,\ \ x_0 \in \ker A.$$

**The norm of a diagonal operator in an orthonormal basis is the supremum of the moduli of its
diagonal entries.** Because the basis is orthonormal, `\|R_z x\|^2` is an *honest sum of squares*
(Parseval), each coefficient `|z-\lambda_k|^{-1}` is bounded by `1/\operatorname{dist}(z,\sigma(A))`,
and the bound follows immediately. Orthogonality is exactly what fails for non-normal operators and
is exactly what makes the geometric bound sharp here.

## Complete Proof

**Setup and spectral theorem.** Let `A : H \to H` be compact and Hermitian (`A = A^*`) on a complex
Hilbert space. The spectral theorem for compact self-adjoint operators gives an orthonormal system
`\{e_k\}_{k \in J}` (`J` finite or countable) with `A e_k = \lambda_k e_k`, each `\lambda_k \in \mathbb{R}\setminus\{0\}`,
`\lambda_k \to 0` if `J` is infinite, such that every `x \in H` decomposes orthogonally as

$$x = x_0 + \sum_{k} \langle x, e_k\rangle e_k, \qquad x_0 \in \ker A, \qquad
Ax = \sum_k \lambda_k \langle x, e_k\rangle e_k.$$

The spectrum is `\sigma(A) = \{\lambda_k : k \in J\} \cup Z`, where `0 \in Z` precisely when
`\ker A \ne \{0\}` or `J` is infinite (in which case `0` is an eigenvalue or an accumulation point of
the `\lambda_k`); the `\lambda_k` and (when present) `0` are exactly the spectral points.

**Trivial case `z \in \sigma(A)`.** Then `\operatorname{dist}(z, \sigma(A)) = 0`, the right-hand side
is `+\infty`, and the inequality holds vacuously (the resolvent need not even exist).

**Main case `z \notin \sigma(A)`.** Set `d = \operatorname{dist}(z, \sigma(A)) = \inf_{\mu \in \sigma(A)} |z - \mu| > 0`
(the infimum is positive because `\sigma(A)` is closed and `z \notin \sigma(A)`). In particular

$$|z - \lambda_k| \ge d \ \text{ for all } k, \qquad\text{and}\qquad |z| \ge d \ \text{ whenever } 0 \in \sigma(A). \tag{$\ast$}$$

**Diagonalize `z - A`.** Using `Ax_0 = 0`,

$$(z - A)x = z\,x_0 + \sum_k (z - \lambda_k)\langle x, e_k\rangle e_k.$$

Since `z \ne 0` on `\ker A` (if `\ker A \ne \{0\}` then `0 \in \sigma(A)`, so `z \ne 0` as `z \notin \sigma(A)`)
and `z \ne \lambda_k` for all `k`, this is invertible with

$$R_z x = (z - A)^{-1} x = \frac{1}{z}\,x_0 + \sum_k \frac{1}{z - \lambda_k}\,\langle x, e_k\rangle e_k. \tag{1}$$

(The `\tfrac1z x_0` term is present only when `\ker A \ne \{0\}`, in which case `0 \in \sigma(A)` and
`(\ast)` gives `|z| \ge d`.) One checks directly that `(z-A)R_z x = R_z(z-A)x = x`, so (1) is indeed the
resolvent.

**Read off the norm.** The vectors `x_0` and `\{e_k\}` are mutually orthogonal and `\{e_k\}` is
orthonormal, so by the Pythagorean identity / Parseval applied to (1),

$$\|R_z x\|^2 = \frac{1}{|z|^2}\,\|x_0\|^2 + \sum_k \frac{1}{|z - \lambda_k|^2}\,|\langle x, e_k\rangle|^2.$$

By `(\ast)`, every coefficient satisfies `|z|^{-2} \le d^{-2}` (when the `x_0` term occurs) and
`|z - \lambda_k|^{-2} \le d^{-2}`. Therefore

$$\|R_z x\|^2 \le d^{-2}\Big(\|x_0\|^2 + \sum_k |\langle x, e_k\rangle|^2\Big) = d^{-2}\,\|x\|^2,$$

the last equality again by Parseval (`\|x\|^2 = \|x_0\|^2 + \sum_k |\langle x, e_k\rangle|^2`). Taking
square roots,

$$\|R_z x\| \le d^{-1}\,\|x\| \qquad \text{for all } x \in H,$$

so

$$\boxed{\ \|R_z(A)\| \le \frac{1}{d} = \frac{1}{\operatorname{dist}(z, \sigma(A))}.\ }$$

This proves the inequality for all `z \in \mathbb{C}`. ∎

**Remark.** The bound is in fact an equality `\|R_z(A)\| = \operatorname{dist}(z,\sigma(A))^{-1}`,
because the diagonal entry `(z - \mu)^{-1}` with `\mu` the nearest spectral point achieves the supremum
(take `x = e_k` for the nearest eigenvalue, or an approximate eigenvector when the nearest point is `0`).
The equality is the hallmark of **normal** operators; for self-adjoint `A` one even has the stronger
`\|R_z\| \le 1/|\operatorname{Im} z|` for non-real `z`. What makes it all work is orthogonality of the
eigenbasis, which turns `\|R_z x\|^2` into a clean sum of squares — precisely the structure that
non-normal operators lack, and why their resolvents can blow up far from the spectrum.

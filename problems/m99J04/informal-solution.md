<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m99J04: Spectral theorem, and a generalized eigenvalue problem reduced by congruence

## Why It's Hard

The first two parts are foundational, but part (c) is the substance: it is a **generalized eigenvalue
problem** `(T - \lambda P)v = 0` with `P = (A^*)^{-1}A^{-1}` — the operator analogue of the matrix problem
`Tv = \lambda Pv` with `P` positive definite. The difficulty is that `T` alone, while compact and
self-adjoint, is not the operator whose spectral theorem you can quote; the weight `P` is in the way. One
must *transform* the problem into an ordinary eigenvalue problem for a compact self-adjoint operator before
the spectral theorem of part (a) applies. The right transformation is a **congruence** `v = Aw`, which is
exactly what turns `T` and `P` into `A^*TA` and the identity — and `A^*TA` is precisely the compact
self-adjoint operator from part (b).

The final twist is the orthonormality question. The natural basis `\{v_\alpha = Aw_\alpha\}` is **not**
orthonormal in the standard inner product (unless `A` happens to be unitary), because the congruence `A`
distorts angles. It *is* orthonormal in the `P`-weighted inner product — the generalized eigenvalue problem
diagonalizes `T` and `P` simultaneously, but in the geometry defined by `P`, not the original one.

## The Key Insight

Substitute `v = Aw` into `(T - \lambda P)v = 0` and left-multiply by `A^*`:

$$TAw = \lambda (A^*)^{-1}A^{-1}(Aw) = \lambda (A^*)^{-1}w \ \Longrightarrow\ A^*TA\,w = \lambda w.$$

So `v = Aw` solves the generalized problem **iff** `w` is an ordinary eigenvector of `S = A^*TA`. By part (b)
`S` is compact and self-adjoint, so part (a) gives an orthonormal basis `\{w_\alpha\}` of eigenvectors,
`Sw_\alpha = \lambda_\alpha w_\alpha`. Then `\{v_\alpha = Aw_\alpha\}` is a basis (`A` invertible) of
solutions. It is `P`-orthonormal:

$$\langle Pv_\alpha, v_\beta\rangle = \langle (A^*)^{-1}A^{-1}Aw_\alpha, Aw_\beta\rangle
= \langle (A^{-1})^*w_\alpha, Aw_\beta\rangle = \langle w_\alpha, w_\beta\rangle = \delta_{\alpha\beta},$$

but generally **not** orthonormal in `\langle\cdot,\cdot\rangle` (`\langle v_\alpha, v_\beta\rangle = \langle A^*Aw_\alpha, w_\beta\rangle \ne \delta_{\alpha\beta}` unless `A^*A = I`).

## Complete Proof

### (a) Spectral theorem for a compact self-adjoint operator

Let `T : H \to H` be compact and self-adjoint on a Hilbert space `H`. Then:

- every eigenvalue of `T` is **real**;
- eigenvectors for distinct eigenvalues are orthogonal, and each nonzero eigenvalue has finite multiplicity;
- the nonzero eigenvalues form a finite set or a sequence `\lambda_n \to 0`;
- there is an **orthonormal system of eigenvectors** `\{e_n\}` (`Te_n = \lambda_n e_n`, `\lambda_n \in \mathbb R`)
  spanning `(\ker T)^\perp`, such that

$$Tx = \sum_n \lambda_n \langle x, e_n\rangle e_n \qquad (x \in H).$$

Adjoining an orthonormal basis of `\ker T` (eigenvalue `0`) yields an **orthonormal basis of `H` consisting
of eigenvectors of `T`** (for `H` separable); `T` is diagonalized in this basis.

### (b) `A^*TA` is compact and self-adjoint

`A : H \to H` is bounded invertible (so `A` and `A^*` are bounded), and `T` is compact and self-adjoint.

**Compact.** The compact operators form a two-sided ideal in `B(H)`: composing a compact operator with
bounded operators (on either side) yields a compact operator. Since `T` is compact and `A, A^*` are bounded,
`A^*TA = A^* \circ T \circ A` is **compact**.

**Self-adjoint.** Using `(BC)^* = C^*B^*`, `(A^*)^* = A`, and `T^* = T`,

$$(A^*TA)^* = A^*\,T^*\,(A^*)^* = A^*\,T\,A = A^*TA.$$

So `A^*TA` is **self-adjoint**. ∎

### (c) A basis of solutions to `(T - \lambda P)v = 0`, `P = (A^*)^{-1}A^{-1}`

**`P` is positive and self-adjoint.** `P^* = \big((A^*)^{-1}A^{-1}\big)^* = (A^{-1})^*\big((A^*)^{-1}\big)^* = (A^*)^{-1}A^{-1} = P`,
and `\langle Pv, v\rangle = \langle (A^*)^{-1}A^{-1}v, v\rangle = \langle A^{-1}v, A^{-1}v\rangle = \|A^{-1}v\|^2 > 0`
for `v \ne 0`. So `\langle u, v\rangle_P := \langle Pu, v\rangle = \langle A^{-1}u, A^{-1}v\rangle` is an inner
product equivalent to the original.

**Reduction by congruence.** Put `v = Aw` (a bijection of `H`, since `A` is invertible). Then

$$(T - \lambda P)v = 0 \iff TAw = \lambda (A^*)^{-1}A^{-1}(Aw) = \lambda (A^*)^{-1}w.$$

Left-multiplying by the invertible `A^*` (which preserves the equation),

$$A^*TA\,w = \lambda\,w, \qquad\text{i.e.}\qquad Sw = \lambda w, \quad S := A^*TA.$$

So `v = Aw` solves the generalized problem precisely when `w` is an eigenvector of `S`.

**Apply the spectral theorem.** By part (b), `S = A^*TA` is compact and self-adjoint, so by part (a) there is
an orthonormal basis `\{w_\alpha\}` of `H` with `Sw_\alpha = \lambda_\alpha w_\alpha`, `\lambda_\alpha \in \mathbb R`.
Setting `v_\alpha = Aw_\alpha`, each satisfies `(T - \lambda_\alpha P)v_\alpha = 0`, and since `A` is
invertible it maps the basis `\{w_\alpha\}` to a **basis `\{v_\alpha\}` of `H`** of solutions.

**Orthonormality.** The basis is `P`-orthonormal:

$$\langle v_\alpha, v_\beta\rangle_P = \langle Pv_\alpha, v_\beta\rangle = \langle A^{-1}v_\alpha, A^{-1}v_\beta\rangle
= \langle w_\alpha, w_\beta\rangle = \delta_{\alpha\beta}.$$

But in the **standard** inner product it is generally *not* orthonormal:

$$\langle v_\alpha, v_\beta\rangle = \langle Aw_\alpha, Aw_\beta\rangle = \langle A^*A\,w_\alpha, w_\beta\rangle,$$

which equals `\delta_{\alpha\beta}` for all `\alpha,\beta` **iff** `A^*A = I`, i.e. iff `A` is unitary.

$$\boxed{\ \{v_\alpha = Aw_\alpha\}\text{ is a basis of solutions of } (T-\lambda_\alpha P)v_\alpha = 0;\
\text{it is orthonormal in } \langle\cdot,\cdot\rangle_P\text{, not in } \langle\cdot,\cdot\rangle\text{ (unless }A\text{ is unitary).}\ }$$

∎

**Remark.** This is the Hilbert-space version of the generalized symmetric eigenvalue problem `Tv = \lambda Pv`
with `P > 0`: the congruence `v = Aw` (where `P = (AA^*)^{-1}`, so `A` is a "square root" of `P^{-1}`)
simultaneously diagonalizes `T` and `P`, converting the pencil `(T, P)` into the ordinary self-adjoint
operator `A^*TA` and the identity. Compactness of `T` (preserved as `A^*TA` by the ideal property) is what
makes the spectral theorem applicable and the eigensolutions a genuine basis. The eigenvectors are
orthonormal in the geometry of `P` — exactly the weighted orthogonality `\langle Pv_\alpha, v_\beta\rangle = \delta_{\alpha\beta}`
familiar from finite-dimensional generalized eigenproblems.

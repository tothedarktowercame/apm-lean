<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96A01: Eigenspaces of a compact operator at nonzero eigenvalues are finite-dimensional

## Why It's Hard

The statement is a cornerstone of the Riesz–Fredholm spectral theory of compact operators, and its
difficulty is conceptual rather than computational: it links an *operator* property (compactness) to a
*dimension* property (finiteness) of a subspace. There is no calculation to do — the whole game is to
recognize which abstract theorem to deploy and to set up the contradiction correctly.

The key obstacle is seeing that on the eigenspace `E_\lambda = \{x : Lx = \lambda x\}` the operator `L`
degenerates into something completely rigid: it acts as multiplication by the scalar `\lambda`. When
`\lambda \ne 0`, this means `L` restricted to `E_\lambda` is essentially the **identity** (up to the
nonzero scalar). But a compact identity operator is the signature of finite dimension — that is exactly
the content of Riesz's theorem. The hypothesis `\lambda \ne 0` is indispensable: dividing by `\lambda` is
what converts "compact" into "identity is compact," and at `\lambda = 0` the kernel `\ker L` can be
infinite-dimensional.

## The Key Insight

On `E_\lambda`, `L` acts as `\lambda \cdot \mathrm{Id}`. So compactness of `L` makes the closed unit ball
of `E_\lambda` relatively compact: any bounded sequence `(x_n)` in `E_\lambda` has, by compactness of `L`,
a subsequence with `Lx_n = \lambda x_n` convergent, hence (dividing by `\lambda \ne 0`) `x_n` itself
convergent. A normed space whose unit ball is (sequentially) compact must be **finite-dimensional**
(Riesz). Equivalently and concretely: if `E_\lambda` were infinite-dimensional, **Riesz's lemma** would
produce unit vectors `x_1, x_2, \dots` with `\|x_n - x_m\| \ge \tfrac12` — a `\tfrac12`-separated bounded
sequence whose image `\lambda x_n` admits no convergent subsequence, contradicting compactness.

## Complete Proof

### (a) Definition

A linear transformation `L : X \to X` of a normed linear space into itself is **compact** if it maps
bounded sets to relatively compact sets; equivalently, the closure `\overline{L(B)}` of the image of the
unit ball `B = \{x : \|x\| \le 1\}` is compact; equivalently, for **every bounded sequence** `(x_n)` in
`X`, the sequence `(Lx_n)` has a convergent subsequence. (Compact operators are automatically bounded.)

### (b) `E_\lambda = \{x : Lx = \lambda x\}` is finite-dimensional (`\lambda \ne 0`)

`E_\lambda = \ker(L - \lambda I)` is a linear subspace of `X`. We show `\dim E_\lambda < \infty`.

**The crucial observation.** For `x \in E_\lambda`, `Lx = \lambda x`. Thus `L` maps `E_\lambda` into
itself, and on `E_\lambda`,

$$L\big|_{E_\lambda} = \lambda\,\mathrm{Id}_{E_\lambda}.$$

**Sequential compactness of the unit ball of `E_\lambda`.** Let `(x_n)` be any bounded sequence in
`E_\lambda`. By compactness of `L` (a bounded sequence in `X`), `(Lx_n)` has a convergent subsequence
`Lx_{n_k} \to z`. But `Lx_{n_k} = \lambda x_{n_k}`, so `x_{n_k} = \tfrac1\lambda Lx_{n_k} \to \tfrac1\lambda z`
(here `\lambda \ne 0` is used). Hence every bounded sequence in `E_\lambda` has a convergent subsequence:
the closed unit ball of `E_\lambda` is sequentially compact.

**Riesz's theorem forces finite dimension.** A normed linear space whose closed unit ball is (sequentially)
compact is finite-dimensional. We prove the contrapositive directly using **Riesz's lemma**:

> *Riesz's lemma.* If `Y` is a proper closed subspace of a normed space `Z` and `0 < \theta < 1`, there
> exists `x \in Z` with `\|x\| = 1` and `\operatorname{dist}(x, Y) \ge \theta`.
> *(Proof: pick `z \notin Y`, let `d = \operatorname{dist}(z,Y) > 0`; choose `y_0 \in Y` with
> `\|z - y_0\| \le d/\theta`; set `x = (z-y_0)/\|z-y_0\|`. For any `y \in Y`,
> `\|x - y\| = \|z - (y_0 + \|z-y_0\|y)\| / \|z-y_0\| \ge d/(d/\theta) = \theta`, since
> `y_0 + \|z-y_0\|y \in Y`.)*

Suppose, for contradiction, that `E_\lambda` is infinite-dimensional. Build unit vectors inductively: given
`x_1, \dots, x_n \in E_\lambda`, the span `Y_n = \operatorname{span}\{x_1,\dots,x_n\}` is finite-dimensional,
hence closed, and a *proper* subspace of the infinite-dimensional `E_\lambda`. By Riesz's lemma (with
`\theta = \tfrac12`) choose `x_{n+1} \in E_\lambda` with `\|x_{n+1}\| = 1` and
`\operatorname{dist}(x_{n+1}, Y_n) \ge \tfrac12`. In particular

$$\|x_n - x_m\| \ge \tfrac12 \qquad \text{for all } n \ne m.$$

This `(x_n)` is bounded (`\|x_n\| = 1`) but has no Cauchy — hence no convergent — subsequence. Yet by the
previous step it *must* have a convergent subsequence. Contradiction.

Therefore `E_\lambda` is finite-dimensional:

$$\boxed{\ \dim\{x \in X : Lx = \lambda x\} < \infty \quad (\lambda \ne 0).\ }\qquad\blacksquare$$

**Remark.** The mechanism is "`L` compact `\Rightarrow` identity compact on `E_\lambda` `\Rightarrow`
`E_\lambda` finite-dimensional." The nonzero scalar `\lambda` is what lets the compactness of `L` transfer
to the identity (one divides by `\lambda`); this fails at `\lambda = 0`, where `\ker L` may be
infinite-dimensional (e.g. a projection of infinite-dimensional kernel is compact only if its range is
finite-dimensional, but the point stands that `0`-eigenspaces are unconstrained). This finite-dimensionality
of nonzero eigenspaces is the first step of the Fredholm alternative and of the spectral theorem for
compact operators.

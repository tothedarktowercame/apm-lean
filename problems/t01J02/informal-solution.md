<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01J02: A covering map induces isomorphisms on higher homotopy groups πₙ (n ≥ 2)

## Why It's Hard

The statement looks like it should follow from "covering maps are nice for `\pi_1`," but the behavior on
`\pi_n` is the *opposite* of the `\pi_1` case: a covering `p` is generally **not** surjective on `\pi_1`
(e.g. `\mathbb R \to S^1`), yet it is an **isomorphism** on every `\pi_n` with `n \ge 2`. The whole
distinction turns on one fact — `S^n` is **simply connected for `n \ge 2`** but not for `n = 1` — and the
difficulty is knowing exactly *where* in the proof this enters and which covering-space tool to deploy on
each half:

- **Surjectivity** is a **lifting** problem: given `\gamma : S^n \to X`, can you lift it to `\tilde X`? The
  lifting criterion says yes iff `\gamma_*(\pi_1 S^n) \subseteq p_*(\pi_1\tilde X)`. For `n \ge 2` the left
  side is `0` (since `\pi_1(S^n) = 0`), so the obstruction *vanishes automatically* — this is the only
  place `n \ge 2` is used, and it is exactly what fails for `n = 1`.
- **Injectivity** is a **homotopy-lifting** problem: a null-homotopy of `p\circ\alpha` downstairs must be
  lifted to a null-homotopy of `\alpha` upstairs. The subtlety is controlling the *endpoint* of the lifted
  homotopy: it lands in the discrete fiber `p^{-1}(x_0)`, and one must argue (connectedness of `S^n` +
  unique lifting of the constant basepoint path) that it is the *constant* map at `\tilde x_0`, not merely
  fiber-valued.

Mishandling basepoints, or forgetting that the lifted endpoint map is fiber-valued-hence-constant, are the
classic errors.

## The Key Insight

Two covering-space tools, each applied to one direction, with `S^n` (`n\ge 2`) simply connected as the
hinge:

- **Surjectivity via the lifting criterion.** Any `\gamma : (S^n, s_0) \to (X, x_0)` lifts to
  `\tilde\gamma : (S^n, s_0) \to (\tilde X, \tilde x_0)` because `\pi_1(S^n) = 0` makes the lifting
  obstruction trivial; then `p_*[\tilde\gamma] = [\gamma]`.
- **Injectivity via the homotopy lifting property.** If `p\circ\alpha` is null-homotopic (rel `s_0`), lift
  the null-homotopy starting from `\alpha`; its time-`1` slice is a continuous map `S^n \to p^{-1}(x_0)`
  into a **discrete** set, hence constant, and basepoint tracking pins that constant at `\tilde x_0`. So
  `\alpha` is null-homotopic and `\ker p_* = 0`.

## Complete Proof

We use three standard facts about a covering projection `p : (\tilde X, \tilde x_0) \to (X, x_0)`:

1. **(Homotopy Lifting Property)** `p` is a fibration: for any space `A`, given a homotopy `H : A\times I \to
   X` and a lift `\tilde h_0 : A \to \tilde X` of `H(\cdot, 0)`, there is a unique lift `\tilde H : A\times I
   \to \tilde X` with `\tilde H(\cdot,0) = \tilde h_0` and `p\circ\tilde H = H`.
2. **(Unique Path Lifting)** a lift of a constant path is constant; more generally lifts of paths are unique
   given their starting point.
3. **(Lifting Criterion)** for `A` path-connected and locally path-connected, a map `f : (A, a_0) \to (X,
   x_0)` lifts to `(\tilde X, \tilde x_0)` iff `f_*(\pi_1(A, a_0)) \subseteq p_*(\pi_1(\tilde X, \tilde
   x_0))`.

Also recall: for `n \ge 2`, `S^n` is path-connected, locally path-connected, and **simply connected**
(`\pi_1(S^n, s_0) = 0`). Throughout, maps `(S^n, s_0)\to(X,x_0)` and homotopies are basepoint-preserving (rel
`s_0`), as in the definition of `\pi_n`. Since `p_*` is given to be a homomorphism, it suffices to prove it
is **surjective** and **injective**.

### Surjectivity of `p_*`

Let `[\gamma] \in \pi_n(X, x_0)` be represented by `\gamma : (S^n, s_0) \to (X, x_0)`. Because `n \ge 2`,
$$
\gamma_*\big(\pi_1(S^n, s_0)\big) = \gamma_*(0) = 0 \subseteq p_*\big(\pi_1(\tilde X, \tilde x_0)\big),
$$
so the hypothesis of the **Lifting Criterion** is satisfied (and `S^n` is path-connected and locally
path-connected). Hence `\gamma` lifts to a basepoint-preserving map
$$
\tilde\gamma : (S^n, s_0) \to (\tilde X, \tilde x_0), \qquad p \circ \tilde\gamma = \gamma .
$$
Then `[\tilde\gamma] \in \pi_n(\tilde X, \tilde x_0)` and
$$
p_*[\tilde\gamma] = [p\circ\tilde\gamma] = [\gamma].
$$
Thus every class in `\pi_n(X, x_0)` is in the image, and `p_*` is surjective. (This is the unique step using
`n \ge 2`; for `n = 1` the inclusion `\gamma_*(\pi_1 S^1) \subseteq p_*(\pi_1\tilde X)` can fail, and indeed
`p_*` need not be onto.)

### Injectivity of `p_*`

Since `p_*` is a homomorphism, it suffices to show `\ker p_* = 0`. Let `[\alpha] \in \pi_n(\tilde X, \tilde
x_0)`, represented by `\alpha : (S^n, s_0) \to (\tilde X, \tilde x_0)`, with
$$
p_*[\alpha] = [p\circ\alpha] = 0 \in \pi_n(X, x_0).
$$
This means `p\circ\alpha` is null-homotopic rel `s_0`: there is a homotopy
$$
H : S^n \times I \to X, \quad H(\cdot, 0) = p\circ\alpha, \quad H(\cdot, 1) \equiv x_0, \quad H(s_0, t) = x_0\ \forall t .
$$

**Lift the null-homotopy.** The map `\alpha` is a lift of `H(\cdot, 0) = p\circ\alpha`. By the **Homotopy
Lifting Property** (with `A = S^n`), there is a lift
$$
\tilde H : S^n \times I \to \tilde X, \qquad \tilde H(\cdot, 0) = \alpha, \qquad p\circ\tilde H = H .
$$

**The basepoint stays put.** For fixed `s_0`, the path `t \mapsto \tilde H(s_0, t)` is a lift of the constant
path `t\mapsto H(s_0,t) = x_0`, starting at `\tilde H(s_0, 0) = \alpha(s_0) = \tilde x_0`. By **unique path
lifting**, a lift of a constant path is constant, so
$$
\tilde H(s_0, t) = \tilde x_0 \qquad \text{for all } t. \tag{$\ast$}
$$

**The time-1 slice is constant.** The map `\tilde H(\cdot, 1) : S^n \to \tilde X` lifts `H(\cdot, 1) \equiv
x_0`, so its image lies in the fiber `p^{-1}(x_0)`, which is a **discrete** subspace of `\tilde X` (a defining
property of covering projections). Since `S^n` is connected and `\tilde H(\cdot, 1)` is continuous into a
discrete set, it is **constant**, equal to its value at `s_0`, which by `(\ast)` is `\tilde H(s_0, 1) =
\tilde x_0`. Hence
$$
\tilde H(\cdot, 1) \equiv \tilde x_0 .
$$

**Conclude.** `\tilde H` is therefore a basepoint-preserving homotopy (by `(\ast)`, `\tilde H(s_0,t) = \tilde
x_0` throughout) from `\tilde H(\cdot, 0) = \alpha` to the constant map `\tilde H(\cdot,1)\equiv\tilde x_0`.
So `\alpha` is null-homotopic rel `s_0`, i.e. `[\alpha] = 0` in `\pi_n(\tilde X, \tilde x_0)`. Thus `\ker p_*
= 0` and `p_*` is injective.

### Conclusion

`p_* : \pi_n(\tilde X, \tilde x_0) \to \pi_n(X, x_0)` is a homomorphism that is both surjective and
injective, hence an **isomorphism**, for every `n \ge 2`. ∎

**Remark.** The proof isolates the role of the dimension precisely: `n \ge 2` is used *only* to make `S^n`
simply connected, which clears the lifting obstruction for **surjectivity**. Injectivity needs only that
`S^n` is connected (so the lifted endpoint, valued in the discrete fiber, is constant) and the homotopy
lifting property — both available already for `n = 1`. This is why a covering induces an isomorphism on all
*higher* homotopy: a covering is a local homeomorphism, so it cannot change anything that simply-connected
test spheres detect — in particular the universal cover `\tilde X` has `\pi_n(\tilde X) \cong \pi_n(X)` for
`n \ge 2` while killing `\pi_1`, which is exactly how higher homotopy groups of `X` are computed from those
of its universal cover.

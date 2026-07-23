<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00J01: Three false claims, each a near-miss of a real theorem

## Why It's Hard

All three statements sound plausible because each is a *distortion of a genuine theorem*, and the skill is
recognizing exactly which true result is being misquoted and producing a clean counterexample. (a) confuses
"has an orientation double cover" (always true) with "is orientable" (false). (b) confuses the Lefschetz
number with something that ought to be `1`, when in fact for the identity it is the **Euler characteristic**.
(c) drops the *signs* from the degree formula: the **signed** preimage count is a regular-value invariant
(that is the foundational theorem of degree theory), but the raw cardinality is not, because folding maps
redistribute preimages in cancelling `\pm` pairs. The difficulty is resisting the pull of the nearby true
statement and pinpointing where the hypothesis is too weak.

## The Key Insight

- **(a) False.** Orientability is not automatic in any dimension `\ge 2`. The product of a non-orientable
  surface with a circle, `K \times S^1` (`K` the Klein bottle), is a non-orientable `3`-manifold.
- **(b) False.** The Lefschetz number `L(f) = \sum_k (-1)^k \operatorname{tr}(f_* : H_k(X;\mathbb Q) \to H_k(X;\mathbb Q))`
  is a diffeomorphism invariant, but for `f = \mathrm{id}` it equals `\chi(X)`. Take `X = S^2`: `L(\mathrm{id}) = \chi(S^2) = 2 \ne 1`.
- **(c) False.** What is invariant is the **degree** `\deg f = \sum_{x \in f^{-1}(y)} \operatorname{sign}\det df_x`,
  not `|f^{-1}(y)|`. A degree-`1` folding map of `S^1` can hit one regular value `3` times and another once.

## Complete Proof

### (a) "Every three-dimensional manifold is orientable." — FALSE

Let `K` be the Klein bottle, a closed non-orientable `2`-manifold, and consider `M = K \times S^1`, a smooth
closed `3`-manifold. A product `A \times B` is orientable **iff** both factors are orientable (an orientation
of the product restricts to orientations of the factors, and conversely). Since `K` is non-orientable, `M = K \times S^1`
is a **non-orientable** `3`-manifold. Hence not every `3`-manifold is orientable. (Other examples: the twisted
`S^2`-bundle over `S^1`, i.e. the mapping torus of an orientation-reversing diffeomorphism of `S^2`.) The true
nearby fact is only that every manifold admits an *orientation double cover*. ∎

### (b) "A diffeomorphism `f` of a compact oriented `X` has Lefschetz number `1`." — FALSE

The Lefschetz number is `L(f) = \sum_k (-1)^k \operatorname{tr}\big(f_* : H_k(X;\mathbb Q) \to H_k(X;\mathbb Q)\big)`.
Take `f = \mathrm{id}_X`, which is a diffeomorphism. Then `f_* = \mathrm{id}` on every `H_k`, so
`\operatorname{tr}(f_*) = \dim_{\mathbb Q} H_k(X;\mathbb Q) = b_k`, and

$$L(\mathrm{id}_X) = \sum_k (-1)^k b_k = \chi(X),$$

the Euler characteristic. For `X = S^2` (compact, oriented), `\chi(S^2) = 2`, so `L(\mathrm{id}_{S^2}) = 2 \ne 1`.
Hence the claim is false. (The genuine theorem is the **Lefschetz fixed-point theorem**: `L(f) \ne 0` forces
`f` to have a fixed point; there is no reason for `L(f)` to equal `1`, and `L(\mathrm{id}) = \chi` shows it can
be any Euler characteristic.) ∎

### (c) "Regular values of `f : X \to Y` (compact connected oriented, equal dimension) have preimages of equal cardinality." — FALSE

The theorem behind this is that the **signed** count `\deg f = \sum_{x \in f^{-1}(y)} \operatorname{sign}\det(df_x)`
is independent of the regular value `y` (Brouwer degree). The statement drops the signs, and the *unsigned*
cardinality is not invariant.

**Counterexample.** Let `X = Y = S^1`, and define `f : S^1 \to S^1` via the lift `\varphi : \mathbb R \to \mathbb R`,

$$\varphi(\theta) = \theta + a\sin\theta \quad (a > 1), \qquad \varphi(\theta + 2\pi) = \varphi(\theta) + 2\pi,$$

so `f` is a smooth degree-`1` self-map of `S^1`. Since `\varphi'(\theta) = 1 + a\cos\theta` changes sign (as
`a > 1`), `\varphi` is **non-monotone**: it increases, turns back, and increases again over one period. Its
image therefore covers a band of target values **three times** (once on each monotone arc, with local
slopes `+, -, +`) and the rest of the circle **once**.

Pick a regular value `y_0` in the triple-covered band: `|f^{-1}(y_0)| = 3` (with `\varphi' \ne 0` at each
preimage, signs `+, -, +`, net `\deg = 1`). Pick a regular value `y_1` outside the band: `|f^{-1}(y_1)| = 1`
(`\deg = 1`). Both `y_0, y_1` are regular (regular values avoid the finitely many critical values), yet

$$|f^{-1}(y_0)| = 3 \ne 1 = |f^{-1}(y_1)|.$$

So the cardinalities differ. (What *is* true: the signed counts agree — both equal `\deg f = 1` — and the
unsigned counts agree only **mod 2**, since they differ by cancelling `+/-` pairs. The fold creates a `-`
preimage that the cardinality count cannot see.) ∎

**Summary.** All three are **false**. Each strips a hypothesis or a sign from a correct theorem: orientability
is genuinely a nontrivial condition (`K \times S^1` fails it); the Lefschetz number of a diffeomorphism is a
homotopy invariant equal to `\chi(X)` for the identity, not `1`; and it is the *signed* preimage count
(degree), not the cardinality, that is constant across regular values.

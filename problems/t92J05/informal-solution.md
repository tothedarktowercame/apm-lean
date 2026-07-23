<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t92J05: Fundamental groups of RP², S²×S¹, and the genus-2 surface

## Why It's Hard

The task is to *name* three fundamental groups, but each requires invoking a different standard tool, and the
challenge is recognizing which one applies. `\mathbb{RP}^2` calls for **covering-space theory** (its universal
cover is the sphere with a `\mathbb Z/2` deck group); `S^2 \times S^1` calls for the **product formula**
together with the fact that the `2`-sphere is simply connected (so only the circle factor contributes); and
the genus-`2` surface calls for the **van Kampen / CW** computation that gives the one-relator presentation
from its `4g`-gon. The traps are forgetting that `S^2` contributes nothing, and mis-stating the genus-`2`
relator (it is a *product of commutators*, not a single commutator, and the group is nonabelian).

## The Key Insight

- **`\mathbb{RP}^2`:** universal cover `S^2 \to \mathbb{RP}^2` (a `2`-fold cover by a simply connected space)
  has deck group `\mathbb Z/2`, so `\pi_1 = \mathbb Z/2`.
- **`S^2 \times S^1`:** `\pi_1(A\times B) = \pi_1(A)\times\pi_1(B)`, and `\pi_1(S^2) = 1`, `\pi_1(S^1) = \mathbb Z`,
  so `\pi_1 = \mathbb Z`.
- **Genus-`2` surface `\Sigma_2`:** built from a wedge of `2g = 4` circles with one `2`-cell attached along the
  product of commutators, so `\pi_1 = \langle a_1, b_1, a_2, b_2 \mid [a_1,b_1][a_2,b_2] = 1\rangle`.

## Complete Proof

### (a) `\mathbb{RP}^2`

`\mathbb{RP}^2 = S^2 / (x \sim -x)`, and the quotient map `p : S^2 \to \mathbb{RP}^2` is a `2`-fold covering.
Since `S^2` is simply connected (every loop on the sphere contracts), `p` is the **universal cover**, and for a
universal cover the fundamental group of the base is the deck transformation group — here `\{\mathrm{id}, \text{antipodal}\} \cong \mathbb Z/2`.

$$\boxed{\ \pi_1(\mathbb{RP}^2) = \mathbb Z/2.\ }$$

(Equivalently, the CW structure `e^0 \cup e^1 \cup e^2` attaches the `2`-cell along `a^2`, giving the
presentation `\langle a \mid a^2\rangle = \mathbb Z/2`.)

### (b) `S^2 \times S^1`

The fundamental group of a product is the product of the fundamental groups,
`\pi_1(A \times B) \cong \pi_1(A) \times \pi_1(B)`. Here `\pi_1(S^2) = 1` (the sphere is simply connected) and
`\pi_1(S^1) = \mathbb Z`, so

$$\boxed{\ \pi_1(S^2 \times S^1) = 1 \times \mathbb Z \cong \mathbb Z.\ }$$

(The `S^2` factor contributes nothing; the generator is the circle `\{pt\} \times S^1`.)

### (c) The closed oriented surface of genus `2`

The genus-`2` surface `\Sigma_2` is obtained from a regular `4g = 8`-gon (here `8`-gon) by identifying its
edges according to the word `a_1 b_1 a_1^{-1} b_1^{-1} a_2 b_2 a_2^{-1} b_2^{-1}`. Its CW structure has one
`0`-cell, `2g = 4` `1`-cells (`a_1, b_1, a_2, b_2`), and one `2`-cell attached along that word; the
`1`-skeleton is a wedge of `4` circles with `\pi_1 = F_4`. By van Kampen, attaching the `2`-cell adds the
single relation given by the attaching word, so

$$\boxed{\ \pi_1(\Sigma_2) = \langle a_1, b_1, a_2, b_2 \mid [a_1, b_1][a_2, b_2] = 1\rangle,\ }$$

where `[a_i, b_i] = a_i b_i a_i^{-1} b_i^{-1}`. This group is nonabelian, with abelianization
`H_1(\Sigma_2) = \mathbb Z^4`.

**Remark.** Three different mechanisms, one per space: a simply connected universal cover converts a covering's
deck group into `\pi_1` (`\mathbb{RP}^2`); the product formula isolates the only non-simply-connected factor
(`S^2 \times S^1`); and the polygon/CW presentation reads `\pi_1` off the edge-identification word
(`\Sigma_2`). The genus-`g` analogue is `\langle a_1,b_1,\dots,a_g,b_g \mid \prod_{i=1}^g [a_i,b_i]\rangle`,
with abelianization `\mathbb Z^{2g}`; `g=1` recovers the torus `\langle a,b \mid [a,b]\rangle = \mathbb Z^2`.

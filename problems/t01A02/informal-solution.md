<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t01A02: A non-surjective torus map that factors through the (Z/2)²-cover has a fixed point

## Why It's Hard

This problem chains three ideas into a Lefschetz fixed-point argument, and the cleverness is in how the two
hypotheses on `f` — non-surjective, *and* factoring through a specific `4`-fold cover — feed *different*
pieces of the Lefschetz number `L(f) = \sum_k (-1)^k \operatorname{tr}(f_* : H_k(T) \to H_k(T))`. Part (a)
uses non-surjectivity to kill the `H_2` term (degree `0`). Part (c) uses the factoring to control the parity
of the `H_1` term. Neither hypothesis alone suffices: a generic non-surjective torus map can have `L(f) = 0`
and no fixed point, and a map factoring through the cover need not have the `H_2` term vanish. Only together
do they force `L(f) = 1 - (\text{even}) + 0 = \text{odd} \ne 0`.

The subtle step is part (c): one must recognize that the covering map `p : S \to T` (the "double in each
direction" torus cover) induces **multiplication by `2`** on `H_1`, so any map factoring through it has
`f_*|_{H_1}` with all entries even, hence even trace. Parity — not the exact value — is what clinches the
nonvanishing of `L(f)`.

## The Key Insight

`H_*(T) = (\mathbb Z, \mathbb Z^2, \mathbb Z)`, so `L(f) = 1 - \operatorname{tr}(f_*|_{H_1}) + \operatorname{tr}(f_*|_{H_2})`.

- **(a)** Non-surjective `\Rightarrow f` factors through `T \setminus \{q\} \simeq S^1 \vee S^1`, which has
  `H_2 = 0`; so `f_*|_{H_2} = 0`.
- **(b)** The cover `S \to T` with group `(\mathbb Z/2)^2` is `p(z,w) = (z^2, w^2)` on `T = S^1 \times S^1`
  (deck group `= \{(z,w)\mapsto(\pm z, \pm w)\} = \mathbb Z/2 \oplus \mathbb Z/2`); on `H_1` it is `p_* = 2I`.
- **(c)** If `f = p \circ \alpha`, then `f_*|_{H_1} = p_*\,\alpha_* = 2\alpha_*` has **even trace**. Combined
  with (a), `L(f) = 1 - (\text{even}) + 0` is **odd**, hence nonzero, so by Lefschetz `f` has a fixed point.

## Complete Proof

`T = S^1 \times S^1` has `H_0(T) = \mathbb Z`, `H_1(T) = \mathbb Z^2`, `H_2(T) = \mathbb Z`.

### (a) `f_* : H_2(T) \to H_2(T)` is zero

Since `f` is not surjective, choose `q \notin f(T)`; then `f` factors as
`T \xrightarrow{g} T \setminus \{q\} \xhookrightarrow{\iota} T`. The punctured torus deformation retracts onto
its `1`-skeleton, a wedge of two circles: `T \setminus \{q\} \simeq S^1 \vee S^1`. Hence
`H_2(T \setminus \{q\}) = H_2(S^1 \vee S^1) = 0`, and on `H_2`,

$$f_* = \iota_* \circ g_*, \qquad g_* : H_2(T) \to H_2(T \setminus \{q\}) = 0,$$

so `f_* = 0` on `H_2(T)`. (Geometrically, `f_*` is multiplication by `\deg f` on `H_2(T) = \mathbb Z`, and a
non-surjective map has degree `0`.) ∎

### (b) A covering of `T` with group `\mathbb Z/2 \oplus \mathbb Z/2`

Let `S = S^1 \times S^1` and define `p : S \to T = S^1 \times S^1` by

$$p(z, w) = (z^2, w^2).$$

Each coordinate map `z \mapsto z^2` is a `2`-fold cover of `S^1`, so `p` is a `4`-fold covering map. It is
**regular** (normal): the deck transformations are `(z,w) \mapsto (\epsilon z, \delta w)` with `\epsilon, \delta \in \{\pm 1\}`
(these are exactly the symmetries permuting the sheets and commuting with `p`), forming the group

$$\{\pm 1\} \times \{\pm 1\} \cong \mathbb Z/2 \oplus \mathbb Z/2.$$

(Equivalently, `p` corresponds to the subgroup `(2\mathbb Z)^2 \le \mathbb Z^2 = \pi_1(T)` with quotient
`\mathbb Z^2/(2\mathbb Z)^2 = (\mathbb Z/2)^2`.) So `S \to T` is a covering with covering group `\mathbb Z/2 \oplus \mathbb Z/2`. ∎

### (c) If `f` factors through `S`, then `f` has a fixed point

Assume `f = p \circ \alpha` for some `\alpha : T \to S` (with `p : S \to T` the cover of part (b)). We compute
the Lefschetz number `L(f) = \sum_k (-1)^k \operatorname{tr}(f_*|_{H_k})`.

**`H_0`:** `T` is connected, so `f_*|_{H_0} = \mathrm{id}` and `\operatorname{tr} = 1`.

**`H_2`:** by part (a), `f_*|_{H_2} = 0`, so `\operatorname{tr} = 0`.

**`H_1`:** the covering map `p(z,w) = (z^2,w^2)` sends each generating loop of `H_1(S) = \mathbb Z^2` to twice
the corresponding generator of `H_1(T)`, so `p_*|_{H_1} = 2I`. Therefore, writing `A = \alpha_*|_{H_1}` (an
integer `2\times 2` matrix),

$$f_*|_{H_1} = p_*|_{H_1} \circ \alpha_*|_{H_1} = 2A,$$

which has all entries even and hence `\operatorname{tr}(f_*|_{H_1}) = 2\operatorname{tr}(A) \in 2\mathbb Z`.

**Lefschetz number.** Combining,

$$L(f) = \operatorname{tr}(f_*|_{H_0}) - \operatorname{tr}(f_*|_{H_1}) + \operatorname{tr}(f_*|_{H_2})
= 1 - 2\operatorname{tr}(A) + 0,$$

an **odd** integer, in particular `L(f) \ne 0`. The torus `T` is a compact finite CW complex and `f` is
continuous, so the **Lefschetz fixed-point theorem** applies: `L(f) \ne 0` implies `f` has a fixed point.

$$\boxed{\ f \text{ has a fixed point.}\ }\qquad\blacksquare$$

**Remark.** The two hypotheses contribute to different summands of `L(f)` and are both essential. Non-surjectivity
forces `\deg f = 0`, removing the `H_2` term; without it, an `H_2`-degree could cancel the rest. Factoring
through the `(\mathbb Z/2)^2`-cover forces `f_*|_{H_1} = 2A`, making `\operatorname{tr}(f_*|_{H_1})` even — and
since `L(f) = 1 - (\text{even}) = \text{odd}`, parity alone guarantees `L(f) \ne 0`. The covering map's
"multiplication by `2`" on `H_1` is the lever: it pins down the parity of the Lefschetz number, which is all
one needs. (A non-surjective torus map that does *not* factor this way — e.g. one with `f_*|_{H_1}` of trace
`1` — can have `L(f) = 0` and be fixed-point-free, so the factoring hypothesis is doing real work.)

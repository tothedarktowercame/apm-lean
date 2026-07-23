<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t95J04: Low-dimensional maps to spheres are null-homotopic, and three distinct 6-manifolds

## Why It's Hard

Part (a) is a non-existence-of-essential-maps statement, and the leverage is the **dimension gap** `k < n`:
a smooth map from a `k`-manifold cannot fill a higher-dimensional sphere, so it misses a point, and a sphere
minus a point is contractible. Recognizing that *smoothness* (via Sard) gives non-surjectivity for free is
the key — a purely continuous map of the same dimensions could be space-filling. Part (b) is a construction
plus a *distinguishing* argument: it is easy to write down simply-connected compact `6`-manifolds, but one
must prove they are pairwise non-diffeomorphic, which requires invariants. The trap is choosing examples that
share homology (e.g. `\mathbb{CP}^3` and `S^2 \times S^4` have identical Betti numbers and need the cup
product to separate); the clean choice uses three manifolds whose **Betti numbers already differ**, so the
elementary, homotopy-invariant homology suffices.

## The Key Insight

- **(a)** `f : M^k \to S^n` smooth with `k < n`: every point of `M` is a critical point (rank `df \le k < n`),
  so by **Sard** the image `f(M)` has measure zero and `f` misses some `q \in S^n`. Then
  `f` lands in `S^n \setminus \{q\} \cong \mathbb R^n`, contractible — so `f` is null-homotopic.
- **(b)** Take `S^6`, `\mathbb{CP}^3`, `S^3 \times S^3`: all compact, simply connected, dimension `6`. Their
  Betti numbers `(b_0, \dots, b_6)` are
  - `S^6`: `(1,0,0,0,0,0,1)`,
  - `\mathbb{CP}^3`: `(1,0,1,0,1,0,1)`,
  - `S^3 \times S^3`: `(1,0,0,2,0,0,1)`,

  pairwise distinct (compare `b_2` and `b_3`). Homology is a topological invariant, so no two are
  homeomorphic, hence no two are diffeomorphic.

## Complete Proof

### (a) A smooth map `M^k \to S^n` with `k < n` is null-homotopic

Let `M` be a compact `k`-manifold and `f : M \to S^n` smooth with `k < n`.

**Non-surjective (Sard).** At every `x \in M`, `df_x : T_x M \to T_{f(x)}S^n` has rank `\le \dim M = k < n`,
so `df_x` is never onto: every point of `M` is critical and every value `f(x)` is a critical value. By
**Sard's theorem** the set of critical values has measure zero in `S^n`, so `f(M)` has measure zero. Since
`S^n` has positive measure, `f(M) \ne S^n`: there is `q \in S^n \setminus f(M)`.

**Lands in a contractible set.** Thus `f` maps into `S^n \setminus \{q\}`, and stereographic projection from
`q` gives `S^n \setminus \{q\} \cong \mathbb R^n`, which is contractible. Composing `f` with a contraction
homotopy `H` of `S^n \setminus \{q\}` to a point `p_0` yields `\widetilde H(x,t) = H(f(x), t)`, a homotopy from
`f` to the constant map `p_0`. Hence `f` is **null-homotopic**. ∎

(`M` compact is not even needed beyond making `f(M)` an honest measure-zero set; the dimension gap is the
whole point, and the same argument works for any smooth `f : M^k \to S^n` with `k < n`.)

### (b) Three pairwise non-diffeomorphic compact simply-connected 6-manifolds

Take

$$X_1 = S^6, \qquad X_2 = \mathbb{CP}^3, \qquad X_3 = S^3 \times S^3.$$

**These are compact, simply connected, `6`-dimensional.** `S^6` is a compact `6`-manifold, simply connected
(`\pi_1(S^n) = 1` for `n \ge 2`). `\mathbb{CP}^3` is a compact complex `3`-fold (real dimension `6`) and simply
connected (`\mathbb{CP}^n` is). `S^3 \times S^3` is compact of dimension `6` and simply connected (a product of
simply connected spaces is simply connected). ✓

**Their homologies (Betti numbers `b_i = \operatorname{rank} H_i(\cdot;\mathbb Z)`).**

- `S^6`: `H_i = \mathbb Z` for `i = 0, 6` and `0` otherwise — `(b_0,\dots,b_6) = (1,0,0,0,0,0,1)`.
- `\mathbb{CP}^3`: `H_i = \mathbb Z` in even degrees `i = 0, 2, 4, 6` and `0` in odd degrees —
  `(1,0,1,0,1,0,1)`.
- `S^3 \times S^3`: by Künneth, `H_i = \mathbb Z, 0, 0, \mathbb Z^2, 0, 0, \mathbb Z` for `i = 0,\dots,6` —
  `(1,0,0,2,0,0,1)`.

**Pairwise non-diffeomorphic.** Singular homology (hence each `b_i`) is a homotopy invariant, so two
homeomorphic — *a fortiori* diffeomorphic — manifolds have equal Betti numbers. But:

- `X_1` vs `X_2`: `b_2(S^6) = 0 \ne 1 = b_2(\mathbb{CP}^3)`;
- `X_1` vs `X_3`: `b_3(S^6) = 0 \ne 2 = b_3(S^3\times S^3)`;
- `X_2` vs `X_3`: `b_2(\mathbb{CP}^3) = 1 \ne 0 = b_2(S^3\times S^3)` (or `b_3`: `0 \ne 2`).

Since each pair differs in some Betti number, no two of `X_1, X_2, X_3` are homeomorphic, hence no two are
diffeomorphic. ∎

**Remark.** Part (a) is the dimension-gap principle: a smooth map from a lower-dimensional manifold can't be
onto a sphere (Sard), and `S^n` minus a point is `\mathbb R^n`. Part (b) leans on homology being a complete
enough invariant *for this choice*: the three manifolds are separated already by Betti numbers, the most
elementary topological invariant, so one never needs the ring structure. (Had one picked `\mathbb{CP}^3` and
`S^2 \times S^4` — both with Betti numbers `(1,0,1,0,1,0,1)` — they would be distinguished only by the cup
product: in `\mathbb{CP}^3` the degree-`2` generator `x` satisfies `x^3 \ne 0`, while in `S^2 \times S^4` the
degree-`2` generator squares to `0`. Choosing `S^3 \times S^3` instead avoids this and keeps the proof at the
level of Betti numbers.)

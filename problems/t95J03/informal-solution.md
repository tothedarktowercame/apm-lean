<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t95J03: Surfaces sharing a common cover with the Klein bottle — parity decides the torus

## Why It's Hard

The set `S_k` is defined by an existential over covers ("there exists a `k`-fold cover of `F` homeomorphic to
a `k`-fold cover of the Klein bottle `K`"), so describing it requires controlling *all* `k`-fold covers of two
surfaces at once. Two invariants must be tracked together. First, **Euler characteristic**: a `k`-fold cover
multiplies `\chi` by `k`, and `\chi(K) = 0`, so any common cover has `\chi = 0`, forcing `\chi(F) = 0` —
hence `F` is the torus `T^2` or `K`. Second, **orientability**: whether `T^2` actually belongs to `S_k` hinges
on whether `K` admits a `k`-fold cover that is *orientable* (a union of tori), and this is governed by a
parity constraint — an orientable cover of the non-orientable `K` must have *even* degree, because it factors
through the orientation double cover. Spotting that the answer depends on the parity of `k`, and proving the
even/odd dichotomy via the orientation character, is the crux.

## The Key Insight

`\chi(K) = 0`, and covers multiply `\chi`, so a common `k`-fold cover has `\chi = 0`; thus
`\chi(F) = 0` and `F \in \{T^2, K\}` (the only closed surfaces with `\chi = 0`).

- `K \in S_k` trivially (a cover of `K` is homeomorphic to itself).
- `T^2 \in S_k` iff `K` has a `k`-fold cover that is a disjoint union of **tori** (orientable). A connected
  *orientable* cover of `K` has **even** degree — it factors through the orientation double cover `T^2 \to K`,
  so its degree is `2 \cdot (\text{something})`. Hence:
  - **`k` even:** `K` has a connected `k`-fold cover `\cong T^2`, and so does `T^2`; so `T^2 \in S_k`.
  - **`k` odd:** every `k`-fold cover of `K` has odd total degree, so it cannot be a union of even-degree torus
    components only — it must contain a non-orientable `(K)` component — so it is not homeomorphic to any cover
    of `T^2` (which is all tori); thus `T^2 \notin S_k`.

$$\boxed{\ S_k = \begin{cases} \{T^2,\ K\} & k \text{ even}, \\ \{K\} & k \text{ odd}. \end{cases}}$$

## Complete Proof

Throughout, "surface" means a closed surface; `K` is the Klein bottle, `T^2` the torus.

**Step 1 — `S_k \subseteq \{T^2, K\}`.** A `k`-fold cover of a closed surface multiplies the Euler
characteristic by `k` (lift a CW structure: `k` times as many cells in each dimension; for a disconnected
cover the total `\chi` still multiplies). Since `\chi(K) = 0`, every `k`-fold cover `E_K` of `K` has
`\chi(E_K) = 0`. If `F \in S_k`, some `k`-fold cover `E_F` of `F` is homeomorphic to such an `E_K`, so
`k\,\chi(F) = \chi(E_F) = \chi(E_K) = 0`, giving `\chi(F) = 0`. The only closed surfaces with `\chi = 0` are
`T^2` and `K`. So `S_k \subseteq \{T^2, K\}`.

**Step 2 — `K \in S_k`.** Any `k`-fold cover of `K` is (trivially) homeomorphic to a `k`-fold cover of `K`
(itself). So `K \in S_k` for every `k > 1`.

**Step 3 — Connected orientable covers of `K` have even degree.** Write
`\pi_1(K) = \langle a, b \mid bab^{-1} = a^{-1}\rangle`, with orientation character `w_1 : \pi_1(K) \to \mathbb Z/2`,
`w_1(a) = 0`, `w_1(b) = 1` (the `b`-loop reverses orientation). Its kernel `\ker w_1 = \langle a, b^2\rangle \cong \mathbb Z^2`
has index `2` and is `\pi_1(T^2)`; the corresponding double cover is the orientation cover `T^2 \to K`. A
connected `d`-fold cover of `K` corresponds to an index-`d` subgroup `H \le \pi_1(K)`, and its total space is
**orientable** iff `H \subseteq \ker w_1`. In that case

$$d = [\pi_1(K) : H] = [\pi_1(K) : \ker w_1]\,[\ker w_1 : H] = 2\,[\ker w_1 : H],$$

so `d` is **even**. Conversely, for any even `d = 2m`, `\ker w_1 \cong \mathbb Z^2` has a subgroup of index
`m`, which has index `2m = d` in `\pi_1(K)` and lies in `\ker w_1`, giving a connected orientable (`T^2`)
`d`-fold cover. So `K` has a connected `d`-fold cover `\cong T^2` **iff `d` is even**; odd-degree connected
covers of `K` are all `\cong K`.

**Step 4 — `T^2 \in S_k` iff `k` is even.**

*`k` even:* By Step 3, `K` has a connected `k`-fold cover homeomorphic to `T^2`. Also `T^2` has a connected
`k`-fold cover, which (being a connected cover of the orientable `T^2` with `\chi = 0`) is again `T^2`. These
two covers are both `T^2`, hence homeomorphic, so `T^2 \in S_k`.

*`k` odd:* Any `k`-fold cover of `T^2` is a disjoint union of tori (every connected cover of `T^2` is a torus),
in particular **orientable**. Suppose some `k`-fold cover `E_K` of `K` were homeomorphic to it; then `E_K` is
a disjoint union of tori, so *every* component of `E_K` is a connected orientable cover of `K`, hence of even
degree (Step 3). But the degrees sum to `k`, which is odd — a sum of even numbers cannot be odd, contradiction.
So no `k`-fold cover of `K` is all tori, and `T^2 \notin S_k`.

**Conclusion.** Combining Steps 1–4,

$$S_k = \begin{cases} \{T^2,\ K\} & k \text{ even}, \\[2pt] \{K\} & k \text{ odd}. \end{cases}$$

$\blacksquare$

**Remark.** Two invariants do all the work. Euler characteristic confines `S_k` to `\{T^2, K\}` (covers of `K`
have `\chi = 0`). Orientability, refined by the **degree parity**, decides the torus: an orientable cover of
the non-orientable `K` must factor through the orientation double cover and so has even degree, so `K` and
`T^2` can share a (torus) cover exactly when `k` is even. For odd `k`, the non-orientability of `K` is forced
to "survive" into every `k`-fold cover (some component stays a Klein bottle), which a cover of the orientable
torus can never match.

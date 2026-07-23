<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96J02: Finite-index subgroups of the Klein bottle group are ℤ² or the group itself

## Why It's Hard

A finite-index subgroup `H \le G = \pi_1(K)` is an abstract group, and asking for *all possibilities up to
isomorphism* requires a complete classification — neither too few nor too many. The challenge is to find an
invariant that pins down `H`. The cleanest tool is the dictionary between subgroups and covering spaces:
finite-index subgroups of `\pi_1(K)` correspond to finite-sheeted covers of the Klein bottle, which are
*closed surfaces*. Because the Klein bottle has Euler characteristic `0` and covers multiply `\chi` by the
degree, every such cover again has `\chi = 0` — and there are exactly two closed surfaces with `\chi = 0`.
That collapses the answer to two groups. The subtlety is then to confirm *both* occur and to identify which
covers give which (orientable torus vs. non-orientable Klein bottle), which one can also verify purely
algebraically from the extension structure of `G`.

## The Key Insight

`G = \pi_1(K) = \langle a, b \mid bab^{-1} = a^{-1}\rangle`. A finite-index subgroup `H` corresponds to a
connected finite cover `\widetilde K \to K`, which is a **closed surface** with

$$\chi(\widetilde K) = [\,G : H\,]\cdot \chi(K) = [G:H]\cdot 0 = 0.$$

The only closed surfaces with `\chi = 0` are the **torus** `T^2` and the **Klein bottle** `K`. Hence
`H = \pi_1(\widetilde K)` is either

$$H \cong \pi_1(T^2) = \mathbb Z^2 \qquad\text{or}\qquad H \cong \pi_1(K) = G,$$

and both occur (`T^2` is the orientation double cover; `K` covers itself). These are the only possibilities.

## Complete Proof

`K` is a closed surface with `\pi_1(K) = G = \langle a, b \mid bab^{-1} = a^{-1}\rangle` and `\chi(K) = 0`.

### The two possibilities

Let `H \le G` have finite index `n = [G:H]`. By covering-space theory, `H` corresponds to a connected
`n`-sheeted covering `p : \widetilde K \to K` with `\pi_1(\widetilde K) \cong H`. Since `K` is a closed
(compact, boundaryless) surface and `p` is a finite cover, `\widetilde K` is again a **closed surface**, and
lifting a CW structure gives

$$\chi(\widetilde K) = n\,\chi(K) = 0.$$

By the classification of closed surfaces, the surfaces with `\chi = 0` are exactly the **torus** `T^2`
(orientable) and the **Klein bottle** `K` (non-orientable). Therefore `\widetilde K \cong T^2` or
`\widetilde K \cong K`, giving

$$H \cong \pi_1(T^2) = \mathbb Z \oplus \mathbb Z \qquad\text{or}\qquad H \cong \pi_1(K) = G.$$

### Both possibilities occur

- `H \cong \mathbb Z^2`: the subgroup `\langle a, b^2\rangle` has index `2` (the quotient `G/\langle\langle a, b^2\rangle\rangle = \langle b \mid b^2\rangle = \mathbb Z/2`),
  and is abelian, since `b^2 a b^{-2} = b(a^{-1})b^{-1} = a`, so `a` and `b^2` commute; thus
  `\langle a, b^2\rangle \cong \mathbb Z^2`. (This is the orientation double cover `T^2 \to K`.)
- `H \cong G`: the subgroup `\langle a^2, b\rangle` has index `2` (quotient `\langle a \mid a^2\rangle = \mathbb Z/2`),
  and from `bab^{-1} = a^{-1}` we get `ba^2b^{-1} = a^{-2}`, so `\langle a^2, b\rangle = \langle a', b \mid ba'b^{-1} = a'^{-1}\rangle \cong G`.
  (This is the self-cover `K \to K`.)

$$\boxed{\ \text{Every finite-index } H \le G \text{ is isomorphic to } \mathbb Z^2 \text{ or to } G,\ \text{and both occur.}\ }\qquad\blacksquare$$

**Algebraic confirmation.** `\langle a\rangle \cong \mathbb Z` is normal in `G` with `G/\langle a\rangle = \langle b\rangle \cong \mathbb Z`,
so `G` is the extension `1 \to \mathbb Z \to G \to \mathbb Z \to 1` (semidirect, `b` acting by inversion).
For finite-index `H`: `H \cap \langle a\rangle = \langle a^k\rangle \cong \mathbb Z` (finite index in `\langle a\rangle`),
and the image of `H` in `G/\langle a\rangle = \mathbb Z` is `m\mathbb Z \cong \mathbb Z` for some `m \ge 1`. So
`H` is an extension `1 \to \mathbb Z \to H \to \mathbb Z \to 1`, determined by how its `b^m`-type generator
conjugates `a^k`: since `b^m a^k b^{-m} = a^{(-1)^m k}`,

- if `m` is **even**, the action is trivial, `H` is abelian, `H \cong \mathbb Z^2`;
- if `m` is **odd**, the action is inversion, `H \cong \langle a^k, b^m \mid b^m a^k b^{-m} = a^{-k}\rangle \cong G`.

This matches the topological dichotomy: `m` even `\iff` `H \subseteq \ker w_1` (orientation-preserving)
`\iff` the cover is the orientable torus; `m` odd `\iff` the cover is again the Klein bottle.

**Remark.** Both descriptions say the same thing: a finite cover of a surface is a surface, `\chi` multiplies
by the degree, and `\chi = 0` leaves exactly `T^2` and `K`. Orientability (equivalently, the parity of the
`b`-winding `m`, equivalently membership in `\ker w_1`) decides which. So up to isomorphism the finite-index
subgroups of the Klein bottle group are precisely `\mathbb Z^2` and the Klein bottle group itself.

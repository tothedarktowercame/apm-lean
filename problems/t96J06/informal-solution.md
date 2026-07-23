<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96J06: RP¹×RP¹ has odd self-intersection, so it does not bound

## Why It's Hard

The claim is a non-bounding statement: `Z = \mathbb{RP}^1 \times \mathbb{RP}^1` is not the boundary of any
compact `3`-manifold inside `\mathbb{RP}^2 \times \mathbb{RP}^2`. Proving "does not bound" requires an
invariant that *vanishes on boundaries* but is nonzero here. The hint — intersection theory — points to the
right one: the **mod-2 self-intersection number**. The conceptual hurdle is twofold. First, one must work
**mod 2**, because `\mathbb{RP}^2` is non-orientable and integral intersection numbers are not even well
defined; the `\mathbb Z/2` theory is exactly what survives non-orientability. Second, one must know the basic
non-orientable fact that a projective line `\mathbb{RP}^1 \subset \mathbb{RP}^2` has *odd* self-intersection
(two distinct lines meet in one point), and see that the product formula squares this to give `Z` an odd
self-intersection in the `4`-manifold — which a boundary can never have.

## The Key Insight

If `Z` bounded a compact `3`-manifold `W` in `M = \mathbb{RP}^2 \times \mathbb{RP}^2`, then `Z = \partial W`
would be null-homologous mod `2`, `[Z] = 0 \in H_2(M; \mathbb Z/2)`, forcing its mod-`2` self-intersection to
be `Z \cdot Z = [Z]\cdot[Z] = 0`. But by the **product formula** for intersection numbers,

$$Z \cdot Z = (\mathbb{RP}^1 \cdot \mathbb{RP}^1)\,(\mathbb{RP}^1 \cdot \mathbb{RP}^1) = 1 \cdot 1 = 1 \pmod 2,$$

since two distinct projective lines in `\mathbb{RP}^2` meet transversally in exactly **one** point. So
`Z \cdot Z = 1 \ne 0`, contradicting boundedness. Hence `Z` does not bound.

## Complete Proof

Work with mod-`2` (`\mathbb Z/2`) homology and intersection numbers, the correct setting since
`\mathbb{RP}^2` is non-orientable. Let `M = \mathbb{RP}^2 \times \mathbb{RP}^2` (a closed `4`-manifold) and
`Z = \mathbb{RP}^1 \times \mathbb{RP}^1` (a closed `2`-dimensional submanifold).

**Step 1 — Boundaries are null-homologous, hence have zero self-intersection.** Suppose, for contradiction,
that `Z = \partial W` for a compact `3`-manifold-with-boundary `W \subseteq M`. Then `Z` is a mod-`2` boundary,
so its `\mathbb Z/2`-homology class vanishes: `[Z] = 0 \in H_2(M; \mathbb Z/2)`. The mod-`2` self-intersection
number `Z \cdot Z` depends only on the class `[Z]` (it is the value of the `\mathbb Z/2` intersection pairing
`[Z] \cdot [Z]`), so

$$Z \cdot Z = [Z] \cdot [Z] = 0 \cdot 0 = 0 \pmod 2.$$

**Step 2 — Compute the self-intersection geometrically.** Compute `Z \cdot Z` by intersecting `Z` with a
transverse pushoff. In each `\mathbb{RP}^2` factor, choose a second projective line `\ell' = \mathbb{RP}^1{}'`
distinct from `\ell = \mathbb{RP}^1`. Two distinct projective lines in `\mathbb{RP}^2` meet transversally in
**exactly one point** (the projective "two points determine a line / two lines determine a point" duality), so

$$\ell \cdot \ell' = 1 \pmod 2 \qquad\text{in } \mathbb{RP}^2.$$

Let `Z' = \ell' \times \ell'`, a transverse pushoff of `Z = \ell \times \ell` in `M`. Their intersection is

$$Z \cap Z' = (\ell \cap \ell') \times (\ell \cap \ell') = \{pt\} \times \{pt\} = \{\text{one point}\},$$

a single transverse point. Therefore the mod-`2` self-intersection is

$$Z \cdot Z = Z \cdot Z' = (\ell \cdot \ell')(\ell \cdot \ell') = 1 \cdot 1 = 1 \pmod 2.$$

(This is the product formula `(A \times B) \cdot (C \times D) = (A \cdot C)(B \cdot D)`.)

**Step 3 — Contradiction.** Steps 1 and 2 give `0 = Z \cdot Z = 1` in `\mathbb Z/2`, impossible. Hence the
assumption fails:

$$\boxed{\ Z = \mathbb{RP}^1 \times \mathbb{RP}^1 \text{ does not bound a 3-manifold in } \mathbb{RP}^2 \times \mathbb{RP}^2.\ }\qquad\blacksquare$$

**Remark.** Equivalently, `[Z] = [\mathbb{RP}^1] \otimes [\mathbb{RP}^1] = \alpha \otimes \alpha` is a nonzero
class in `H_2(\mathbb{RP}^2 \times \mathbb{RP}^2; \mathbb Z/2)` — by Künneth, `H_2 = \langle \beta\otimes 1,\ \alpha\otimes\alpha,\ 1\otimes\beta\rangle \cong (\mathbb Z/2)^3`,
where `\alpha = [\mathbb{RP}^1]` generates `H_1(\mathbb{RP}^2;\mathbb Z/2)` and `\beta = [\mathbb{RP}^2]`. Since
`[Z] \ne 0`, `Z` is not null-homologous and so cannot be a boundary; the self-intersection computation is the
intersection-theory certificate of this, detecting `[Z] \ne 0` via the nondegenerate mod-`2` Poincaré pairing.
The whole obstruction descends from the single non-orientable fact `\mathbb{RP}^1 \cdot \mathbb{RP}^1 = 1` in
`\mathbb{RP}^2` (the projective line is `\mathbb Z/2`-essential), squared by the product structure. Working mod
`2` is essential: there is no integral version because `\mathbb{RP}^2` is non-orientable.

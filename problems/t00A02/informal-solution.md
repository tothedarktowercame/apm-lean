<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00A02: Coverings of a genus-5 surface, and regular vs. irregular coverings of ℝP² ∨ ℝP²

## Why It's Hard

The three parts test whether you can move fluently between the *geometric* picture of a covering and its
*algebraic* invariants.

- **(a)** "All 10-fold coverings are homeomorphic" sounds like it needs you to enumerate coverings (i.e.
  index-10 subgroups of the genus-5 surface group), which are wildly numerous. The trick is to ignore the
  subgroups entirely: a covering of a surface is again a surface, and a *closed orientable* surface is
  determined up to homeomorphism by **one number** — its Euler characteristic, which multiplies by the
  number of sheets. So every connected 10-fold cover has the same `χ`, hence the same genus, hence is the
  same surface. The only subtlety is justifying the three structural facts (the cover is a closed surface;
  it is orientable; `χ` is multiplicative) and noting the statement needs *connected* coverings.
- **(b)(ii)** The pitfall is conceptual: classifying coverings of `ℝP^2 ∨ ℝP^2` means understanding
  `\pi_1 = \mathbb Z/2 * \mathbb Z/2` and the dictionary {coverings ↔ permutation actions of `\pi_1` on the
  fiber}. The constraint that powers the whole problem is that each generator squares to `1`, so each
  monodromy permutation is an **involution**; and an involution decomposes the fiber into fixed points
  (which lift `ℝP^2` to `ℝP^2`) and 2-cycles (which lift `ℝP^2` to its double cover `S^2`). "Regular vs.
  irregular" then becomes "does the deck group act transitively on the fiber" — i.e. do all sheets look
  alike, or not.

## The Key Insight

- **(a)** Euler characteristic is the complete invariant. For a closed orientable genus-`g` surface
  `\chi = 2 - 2g`; an `n`-sheeted covering multiplies it, `\chi(\widetilde F) = n\,\chi(F)`. With `g=5`,
  `n=10`: `\chi(\widetilde F) = 10(2-10) = -80`, so `\widetilde F` is the closed orientable surface of
  genus `41`, and **all such are homeomorphic** by the classification of surfaces.
- **(b)** Coverings of `\mathbb{RP}^2` come in exactly two connected flavors: `\mathbb{RP}^2` itself
  (1 sheet) and `S^2` (2 sheets, the antipodal cover). A covering of the wedge is assembled from these
  pieces along the fiber over the wedge point, governed by two involutions `\sigma_a, \sigma_b` of the
  4-point fiber. **Fixed point of `\sigma` ⇒ an `\mathbb{RP}^2` lobe; 2-cycle ⇒ an `S^2` lobe.** Choosing
  the two involutions to make the deck group act simply transitively gives a **regular** cover; choosing
  them so the sheets are not all interchangeable gives an **irregular** one.

## Complete Proof

### (a) All (connected) 10-fold coverings of the genus-5 surface are homeomorphic

Let `F` be the closed orientable surface of genus `5`, so `\chi(F) = 2 - 2\cdot 5 = -8`. Let
`p : \widetilde F \to F` be a 10-fold covering. (As is standard, we take covering spaces to be connected;
without this the claim is false — e.g. a disjoint union of a 9-fold and a 1-fold cover is also "10-fold"
but disconnected. See the remark.)

**1. `\widetilde F` is a closed surface.** A covering map is a local homeomorphism, so `\widetilde F` is a
2-manifold without boundary. Since `F` is compact and the covering has finitely many (`10`) sheets,
`\widetilde F` is compact. Hence `\widetilde F` is a *closed* surface.

**2. `\widetilde F` is orientable.** Orientability pulls back along local homeomorphisms: choose an
orientation (a coherent choice of local orientations) on `F`; since `p` is a local homeomorphism, pulling
back through the local inverses of `p` gives a coherent local orientation on `\widetilde F`. (Equivalently,
a connected covering space of an orientable manifold is orientable, because the orientation double cover
of `\widetilde F` is pulled back from that of `F`, which is trivial.) So `\widetilde F` is closed and
orientable.

**3. Euler characteristic multiplies.** Triangulate `F` with `V` vertices, `E` edges, `T` triangles, so
`\chi(F) = V - E + T`. Because `p` is a 10-fold covering, every open simplex of `F` is evenly covered and
has exactly `10` preimage simplices, giving a triangulation of `\widetilde F` with `10V` vertices, `10E`
edges, `10T` triangles. Hence
$$
\chi(\widetilde F) = 10V - 10E + 10T = 10\,\chi(F) = 10\cdot(-8) = -80 .
$$

**4. Classification forces the homeomorphism type.** A closed orientable surface is determined up to
homeomorphism by its genus, equivalently by its Euler characteristic via `\chi = 2 - 2g`. From
`\chi(\widetilde F) = -80` we get genus
$$
\widetilde g = \frac{2 - \chi(\widetilde F)}{2} = \frac{2 - (-80)}{2} = 41 .
$$
Thus *every* connected 10-fold covering `\widetilde F` is homeomorphic to the closed orientable surface
`\Sigma_{41}` of genus `41`. In particular, any two such coverings are homeomorphic to each other. ∎

**Remark.** Connectedness is essential and is the only hypothesis doing work beyond `\chi`: the genus-5
surface group `\pi_1(F)` has many non-conjugate index-10 subgroups (so many distinct *based* coverings),
but they all yield the *same total space* `\Sigma_{41}` because the homeomorphism type of a closed
orientable surface sees only `\chi`.

### (b)(i) A double covering of `\mathbb{RP}^2`

Realize `\mathbb{RP}^2 = S^2/\{x \sim -x\}` as the quotient of the sphere by the antipodal map. The
quotient map
$$
q : S^2 \to \mathbb{RP}^2, \qquad x \mapsto \{x, -x\},
$$
is a **2-fold covering**: every point of `\mathbb{RP}^2` is a pair `\{x,-x\}`, and a small ball `U` around
`x` (disjoint from `-U`) has `q^{-1}(q(U)) = U \sqcup (-U)`, two disjoint open sets each mapped
homeomorphically onto `q(U)`. So `S^2 \xrightarrow{\,q\,} \mathbb{RP}^2` is the desired double cover. (It is
also the universal cover, since `S^2` is simply connected and `\pi_1(\mathbb{RP}^2) = \mathbb Z/2`.)

### (b)(ii) A regular and an irregular 4-fold covering of `X = \mathbb{RP}^2 \vee \mathbb{RP}^2`

**Setup (the algebra).** Write `X = A \vee B` with `A, B` two copies of `\mathbb{RP}^2` joined at the wedge
point `x_0`; let `a, b` be the generators of `\pi_1(A) = \pi_1(B) = \mathbb Z/2`. By van Kampen,
$$
\pi_1(X, x_0) = \mathbb Z/2 * \mathbb Z/2 = \langle a, b \mid a^2 = b^2 = 1\rangle .
$$
A connected `4`-fold covering corresponds to a **transitive action of `\pi_1(X)` on a 4-element fiber**
`\{1,2,3,4\} = p^{-1}(x_0)`, i.e. to a pair of permutations `\sigma_a = \rho(a)`, `\sigma_b = \rho(b)` in
`S_4`. Since `a^2 = b^2 = 1`, each of `\sigma_a, \sigma_b` is an **involution**. The covering space is
built lobe-by-lobe over the fiber:

> Over `A`: a **fixed point** of `\sigma_a` carries a single sheet that maps homeomorphically to `A` — an
> `\mathbb{RP}^2` lobe; a **2-cycle** of `\sigma_a` carries two sheets forming the connected double cover
> `S^2 \to A` (part (i)) — an `S^2` lobe. Likewise over `B` with `\sigma_b`.

Each piece is a genuine covering of its `\mathbb{RP}^2` summand (it *is* either the identity cover or the
antipodal cover of part (i)), and near `x_0` the cover is locally `(\text{disk of }A) \vee (\text{disk of }B)`
mapped homeomorphically at each of the 4 fiber points — so the assembled space is an honest `4`-fold cover.
The cover is **regular** precisely when its deck group acts transitively on the fiber (all sheets are
interchangeable), and **irregular** otherwise.

---

**A regular 4-fold covering.** Take the involutions (with `1=00,\,2=10,\,3=01,\,4=11` thought of as
`\mathbb Z/2\times\mathbb Z/2`, acting by translation):
$$
\sigma_a = (1\,2)(3\,4), \qquad \sigma_b = (1\,3)(2\,4).
$$
These are the images of `a, b` under the abelianization `\pi_1(X) = \mathbb Z/2 * \mathbb Z/2 \twoheadrightarrow
\mathbb Z/2 \times \mathbb Z/2`, so the corresponding subgroup (the kernel) is **normal of index 4** and the
cover is regular, with deck group `\mathbb Z/2 \times \mathbb Z/2` acting simply transitively on the 4
sheets.

*The diagram.* Both `\sigma_a` and `\sigma_b` are fixed-point-free (two 2-cycles each), so there are **no
`\mathbb{RP}^2` lobes** — only spheres:

- Over `A`: two `S^2` lobes, on sheet-pairs `\{1,2\}` and `\{3,4\}`.
- Over `B`: two `S^2` lobes, on sheet-pairs `\{1,3\}` and `\{2,4\}`.

Picture the 4 fiber points as dots and each `S^2` lobe as an edge joining the two dots it covers:
```
        S²(A)
    1 -------- 2
    |          |
S²(B)|          |S²(B)
    |          |
    3 -------- 4
        S²(A)
```
This is a 4-cycle `1\!-\!2\!-\!4\!-\!3\!-\!1` of spheres, alternating `A`-double-covers and `B`-double-covers.
*Why it is a covering:* each edge is the antipodal cover `S^2 \to \mathbb{RP}^2` of its summand, and at each
dot the local picture `(\text{half of an }A\text{-sphere}) \vee (\text{half of a }B\text{-sphere})` maps
homeomorphically to a neighborhood of `x_0`. All four dots play identical roles — the deck group
`\mathbb Z/2\times\mathbb Z/2` permutes them transitively — so the cover is **regular**.

---

**An irregular 4-fold covering.** Take the involutions
$$
\sigma_a = (1\,2)\quad(\text{fixes }3,4), \qquad \sigma_b = (1\,4)(2\,3).
$$
Both are involutions (`\sigma_a^2 = \sigma_b^2 = 1`), and the action is transitive: from `1` we reach `2`
via `\sigma_a`, `4` via `\sigma_b`, and `3` via `\sigma_b` from `2`. So the cover is connected.

*The diagram.* Decompose by lobes:

- Over `A`: `\sigma_a = (1\,2)` has the 2-cycle `\{1,2\}` → one `S^2` lobe; and the **fixed points** `3, 4`
  → two `\mathbb{RP}^2` lobes (sheets `3` and `4` each map identically to `A`).
- Over `B`: `\sigma_b = (1\,4)(2\,3)` is fixed-point-free → two `S^2` lobes, on `\{1,4\}` and `\{2,3\}`.

```
         S²(A)
     1 --------- 2          3 : ℝP²(A)   4 : ℝP²(A)
      \         /            (single-sheet lobes over A)
  S²(B)\       /S²(B)
        4     3
         \___/
       (1–4 and 2–3 are the two B-spheres)
```
More plainly: sheets `1,2` lie on a *sphere* over `A`, while sheets `3,4` lie on *projective-plane* lobes
over `A`; over `B`, sheets `\{1,4\}` and `\{2,3\}` pair into two spheres. *Why it is a covering:* exactly as
before, each lobe is either the identity or the antipodal cover of a summand, and the wedge-point
neighborhoods lift homeomorphically; counting sheets, over `A` we have `2+1+1 = 4` and over `B` we have
`2+2 = 4`, so it is `4`-fold everywhere.

*Why it is irregular.* A deck transformation is a self-homeomorphism of the cover commuting with `p`; it
must therefore send each lobe over `A` to a lobe over `A` of the **same type**. But sheets `1,2` sit on an
`S^2` lobe over `A` while sheets `3,4` sit on `\mathbb{RP}^2` lobes over `A` — structurally different — so
no deck transformation can carry sheet `1` to sheet `3`. Hence the deck group does **not** act transitively
on the fiber, and the covering is **irregular**. (Algebraically: `\sigma_a, \sigma_b` generate a group of
order `8` — one computes `\sigma_a\sigma_b = (1\,4\,2\,3)`, a 4-cycle, with `(1\,2)` giving the dihedral
group `D_4` — which is larger than the degree `4`, so the action is not simply transitive and the
corresponding index-4 subgroup is non-normal.) ∎

**Remark.** The organizing principle throughout is the dictionary *coverings ↔ `\pi_1`-actions on the
fiber*, specialized by the relations `a^2=b^2=1` to *pairs of involutions*. Regularity is normality of the
corresponding subgroup, i.e. transitivity of the deck group — visible in the pictures as "all sheets look
alike" (regular) versus "some sheets sit on spheres, others on projective planes" (irregular). The same
fixed-point/2-cycle bookkeeping classifies *all* finite coverings of `\mathbb{RP}^2 \vee \mathbb{RP}^2`.

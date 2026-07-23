<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t03J05: Product tori in a surface-squared, distinguished by intersection numbers

## Why It's Hard

Both parts ask for explicit embedded tori in a `4`-manifold `F \times F` (or `F^* \times F^*`) and demand a
*proof* that they are distinguished — and the right invariant in both cases is the **algebraic intersection
number**, which for surfaces-in-a-`4`-manifold is a signed count of points. Part (a) is a warm-up: build two
tori as products of curves and compute their intersection via the product formula.

Part (b) is genuinely subtle because of the clause "**not homotopic in any `4`-manifold `X` containing
`F^* \times F^*` as an open subset**." Most invariants of a map `T^2 \to F^* \times F^*` (its `\pi_1`-image,
its homology class) can be *destroyed* by enlarging the ambient space: an open inclusion
`F^* \times F^* \hookrightarrow X` may kill classes or collapse `\pi_1`, so a bigger `X` can make formerly
distinct maps homotopic. One must find an invariant that **no enlargement can touch**. The key realization is
that the intersection number of a torus with a *fixed* closed test torus is (i) a homotopy invariant of the
map and (ii) computed by intersection points that are *localized inside the open set* `F^* \times F^*`, hence
the same integer in every `X`. That combination is exactly what survives "any `X`."

## The Key Insight

Equip `F` with a symplectic basis `a_1, b_1, a_2, b_2 \in H_1(F)` (`a_i \cdot b_i = 1`, all other pairings
`0`). For curves, the **product formula** in a surface-square reads

$$(\alpha \times \beta) \cdot (\gamma \times \delta) = \pm\, (\alpha \cdot \gamma)(\beta \cdot \delta).$$

- **(a)** `T_1 = a_1 \times a_1` and `T_2 = b_1 \times b_1` meet in `(a_1 \cap b_1) \times (a_1 \cap b_1)` =
  one transverse point, so `T_1 \cdot T_2 = \pm(a_1 \cdot b_1)^2 = \pm 1 \ne 0`.
- **(b)** Take `T_1 = a_1 \times a_1`, `T_2 = b_1 \times b_1`, `T_3 = a_2 \times a_2` in `F^* \times F^*`.
  Their intersection numbers with the fixed test tori `b_1\times b_1,\ a_1\times a_1,\ b_2\times b_2` form a
  pattern that separates all three. These intersection counts happen inside the open `F^* \times F^*`, so they
  are the *same integer in every `X`*; and a homotopy in `X` preserves intersection number with a fixed cycle.
  Hence no two `T_i` are homotopic in any `X`.

## Complete Proof

Fix a symplectic basis `a_1, b_1, a_2, b_2` of `H_1(F)` represented by disjointly-supported simple closed
curves with `a_i \cdot b_j = \delta_{ij}` and `a_i \cdot a_j = b_i \cdot b_j = 0`. `F` is oriented, so `F \times F`
and (after removing a point off the curves) `F^* \times F^*` are oriented `4`-manifolds. For oriented curves
`\alpha, \beta, \gamma, \delta`, the product tori `\alpha\times\beta`, `\gamma\times\delta` are embedded,
oriented, and satisfy

$$(\alpha\times\beta) \cap (\gamma\times\delta) = (\alpha\cap\gamma) \times (\beta\cap\delta), \qquad
(\alpha\times\beta)\cdot(\gamma\times\delta) = \pm(\alpha\cdot\gamma)(\beta\cdot\delta), \tag{$\ast$}$$

the count of transverse intersection points, signed by the product orientation.

### (a) Two tori with nonzero intersection number

Define embeddings `T^2 \to F \times F` by

$$f_1(s,t) = (a_1(s),\, a_1(t)) \quad(\text{image } T_1 = a_1 \times a_1), \qquad
f_2(s,t) = (b_1(s),\, b_1(t)) \quad(\text{image } T_2 = b_1 \times b_1).$$

Each is an embedding (a product of embedded circles). By `(\ast)`,

$$T_1 \cdot T_2 = \pm(a_1 \cdot b_1)(a_1 \cdot b_1) = \pm(1)(1) = \pm 1 \ne 0.$$

Concretely, `a_1` and `b_1` meet transversally in one point `p`, so `T_1 \cap T_2 = \{(p,p)\}` is a single
transverse point, with local sign `(a_1\cdot b_1)^2 = +1` up to the global product-orientation sign; either
way the intersection number is `\pm 1`, hence nonzero. ∎

### (b) Three tori, pairwise non-homotopic in any ambient `X`

Choose `x \in F` off all four basis curves, so `a_1, b_1, a_2, b_2 \subset F^* = F \setminus \{x\}`. Define
embeddings `T^2 \to F^* \times F^*` with images

$$T_1 = a_1 \times a_1, \qquad T_2 = b_1 \times b_1, \qquad T_3 = a_2 \times a_2,$$

and consider the fixed closed **test tori** (also in `F^* \times F^*`)

$$D_1 = b_1 \times b_1, \qquad D_2 = a_1 \times a_1, \qquad D_3 = b_2 \times b_2.$$

By `(\ast)` (all curve-intersections computed in `F^*`, where `a_i \cdot b_i = 1` and the other pairings
vanish), the intersection numbers are:

| `\cdot` | `D_1 = b_1\times b_1` | `D_2 = a_1\times a_1` | `D_3 = b_2\times b_2` |
|---|---|---|---|
| `T_1 = a_1\times a_1` | `\pm1` | `0` | `0` |
| `T_2 = b_1\times b_1` | `0` | `\pm1` | `0` |
| `T_3 = a_2\times a_2` | `0` | `0` | `\pm1` |

(e.g. `T_1 \cdot D_1 = \pm(a_1\cdot b_1)^2 = \pm1`; `T_2 \cdot D_1 = \pm(b_1 \cdot b_1)^2 = 0`;
`T_3 \cdot D_1 = \pm(a_2 \cdot b_1)^2 = 0`.) Each `T_i` has intersection `\pm1` with `D_i` and `0` with the
other two test tori, so the three rows are pairwise distinct.

**X-independence of these intersection numbers.** Suppose `F^* \times F^* \subseteq X` is open. Each `T_i` and
each `D_j` is a compact oriented torus *inside the open set* `F^* \times F^*`; perturbing to transverse
position can be done within `F^* \times F^*`, so all intersection points lie in `F^* \times F^*` and their
signed count (using the fixed orientation of `F^* \times F^*`) is the integer in the table — *the same in
every `X`*. Thus `T_i \cdot D_j` is a well-defined `X`-independent integer.

**Homotopy invariance.** The intersection number of a map `g : T^2 \to X` with a *fixed* closed oriented
surface `D_j \subset X` depends only on the homology class `[g] \in H_2(X)` (it is the value of the
intersection pairing against `[D_j]`), hence is a homotopy invariant of `g`. So if `T_i` and `T_k` were
homotopic in `X`, then for every `j`,

$$T_i \cdot D_j = T_k \cdot D_j.$$

**Conclusion.** For each pair `i \ne k` the table gives a column `j` (namely `j = i`) with
`T_i \cdot D_i = \pm 1 \ne 0 = T_k \cdot D_i`. This contradicts the homotopy invariance above. Therefore no two
of `T_1, T_2, T_3` are homotopic in `X` — and since `X` was an arbitrary `4`-manifold containing
`F^* \times F^*` as an open subset,

$$\boxed{\ \text{no two of } T_1, T_2, T_3 \text{ are homotopic in any such } X.\ }\qquad\blacksquare$$

**Remark.** The whole force of part (b) is that intersection number with a *fixed* test torus is the rare
invariant immune to enlarging the ambient manifold: homotopy invariance handles "homotopic in `X`," while the
geometric localization of the intersection points inside the open `F^* \times F^*` handles "for *any* `X`."
Removing the point to form `F^*` is not essential to the intersection computation — it is the framing that
makes "any `X`" the operative quantifier (one cannot, e.g., cap off and change the counts). The pattern is the
identity intersection matrix `T_i \cdot D_j = \pm\delta_{ij}`, the cleanest possible separator.

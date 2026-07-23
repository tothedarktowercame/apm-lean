<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t92J06: The universal cover of S¹∨S¹ (the 4-valent tree) and four non-homeomorphic 3-fold covers

## Why It's Hard

`X = S^1\vee S^1` has `\pi_1(X) = F_2 = \langle a, b\rangle`, the free group on two generators, and its
covers are the *graphs* on which `F_2` acts. The two parts probe this dictionary from opposite ends:

- **(a)** The universal cover is simply connected, hence (being a cover of a graph) a **tree** — but not any
  tree: it must be the **`4`-regular** tree (the Cayley graph of `F_2`), every vertex meeting one incoming
  and one outgoing `a`-edge and one incoming and one outgoing `b`-edge. Drawing "a tree" without the precise
  `4`-valent, two-colored structure misses the point.
- **(b)** is the genuine trap: *every* `3`-fold cover of `X` has the **same Euler characteristic**
  `\chi = 3\cdot\chi(X) = 3\cdot(-1) = -3`, and every *connected* one is homotopy equivalent to
  `\bigvee^4 S^1` (free `\pi_1` of rank `4`). So homotopy type, `\chi`, Betti numbers, and `\pi_1`
  **cannot tell them apart** — to get four *non-homeomorphic* covers you must use finer, genuinely
  *topological* invariants of the graphs: the **number of connected components** and the **graph structure**
  (loops, multi-edges). Since every cover is `4`-valent (no degree-`2` vertices to suppress), homeomorphism
  of these graphs coincides with graph isomorphism, which is what makes the invariants usable.

## The Key Insight

- **(a)** The universal cover is the **infinite `4`-valent tree** `T_4`: one vertex per element of `F_2`,
  with edges to `wa^{\pm1}` and `wb^{\pm1}`; it is the Cayley graph of `F_2`, contractible, with deck group
  `F_2`.
- **(b)** A `3`-fold cover is a pair of permutations `(\sigma_a,\sigma_b)\in S_3\times S_3` (how `a,b`
  permute the `3` sheets), giving a `4`-valent graph with `3` vertices and `6` edges (always `\chi=-3`).
  Distinguish four by coarse-to-fine invariants — number of components (`3, 2, 1, 1`) and number of loops
  (`-, -, 3, 0`):

  | cover | `(\sigma_a,\sigma_b)` | components | loops |
  |:--|:--|:--:|:--:|
  | `Y_1` | `(e,\,e)` | `3` | — |
  | `Y_2` | `((1\,2),\,(1\,2))` | `2` | `0` |
  | `Y_3` | `((1\,2\,3),\,e)` | `1` | `3` |
  | `Y_4` | `((1\,2\,3),\,(1\,2\,3))` | `1` | `0` |

## Complete Proof

Give `X = S^1\vee S^1` the CW structure with one vertex `v` and two oriented edges `a, b` (so `\chi(X) = 1 -
2 = -1`, `\pi_1(X) = F_2 = \langle a, b\rangle`). A covering of `X` is again a graph in which **every vertex
has degree `4`** — one incoming and one outgoing edge of each label `a, b` — and the labeled-oriented edges
record a free `F_2`-action on the fiber.

### (a) The universal covering space

The universal cover `\widetilde X` is simply connected. A cover of a graph is a graph, and a simply
connected graph is a **tree** (no cycles, since a cycle would give a nontrivial loop). The local structure is
forced: each vertex, like `v\in X`, must have exactly one outgoing and one incoming `a`-edge and one
outgoing and one incoming `b`-edge, i.e. **degree `4`**. The unique tree with every vertex of degree `4` is
the **`4`-regular (infinite) tree** `T_4`, which is exactly the **Cayley graph of `F_2`**: vertices are the
words `w\in F_2`, and `w` joins to `wa^{\pm1}` and `wb^{\pm1}`. It is contractible, and the deck group is
`F_2` acting by left multiplication. A sketch (one central vertex, `a`-edges horizontal, `b`-edges vertical,
branching forever):

```
                 |b
            a    o    a
        o---------o---------o
        |b        |b        |b
   a    o    a    o    a    o   a
 ...o---o---o   o---o---o   o---o---o...   (every vertex: 2 a-edges, 2 b-edges; no cycles)
        |b        |b        |b
        o         o         o
                 ...
```

### (b) Four pairwise non-homeomorphic `3`-fold coverings

Label the three sheets `1, 2, 3`; a connected/disconnected `3`-fold cover is given by `(\sigma_a, \sigma_b)
\in S_3\times S_3`, connected iff `\langle\sigma_a,\sigma_b\rangle` acts transitively. In every case the
total space is a graph with `V=3`, `E=6`, so `\chi = 3\cdot(-1) = -3` — *the same for all*. We exhibit four
and then prove no two are homeomorphic.

**`Y_1` — the trivial cover, `(\sigma_a,\sigma_b)=(e,e)`.** Each sheet maps identically, so
$$
Y_1 = X\sqcup X\sqcup X
$$
— three disjoint figure-eights. **`3` components.**

**`Y_2` — connected double cover `\sqcup` figure-eight, `(\sigma_a,\sigma_b)=((1\,2),(1\,2))`.** Sheets
`1,2` form a transitive orbit; sheet `3` is fixed. On `\{1,2\}` both `a` and `b` swap the sheets, so the
component is two vertices joined by a *double* `a`-edge and a *double* `b`-edge (the connected double cover,
`\simeq\bigvee^3 S^1`); sheet `3` is a separate figure-eight. **`2` components, no loops.**
```
   ===a===            a   b
  o========o  (Y_2)   ( o )      figure-eight on vertex 3
   ===b===
```

**`Y_3` — cyclic cover with loops, `(\sigma_a,\sigma_b)=((1\,2\,3),e)`.** `\langle(1\,2\,3)\rangle` is
transitive, so connected. The `a`-edges form a directed triangle `1\to 2\to 3\to 1`; `b` fixes every sheet,
so each vertex carries a `b`-**loop**. **`1` component, `3` loops.**
```
        1
       / \ a          (each vertex i has a b-loop:  i↺ )
   a  /   \
     3-----2
        a
```

**`Y_4` — cyclic cover, loopless, `(\sigma_a,\sigma_b)=((1\,2\,3),(1\,2\,3))`.** Connected (transitive).
Both `a`-edges and `b`-edges form directed triangles `1\to2\to3\to1`; **no loops**. **`1` component, `0`
loops.** (This is the cover associated to the surjection `F_2\twoheadrightarrow\mathbb Z/3`, `a,b\mapsto 1`.)
```
        1
      a/b\           a-triangle and b-triangle on the same 3 vertices,
      /   \          no edge from a vertex to itself
     3-----2
      a/b
```

### Why no two are homeomorphic

These are finite graphs in which **every vertex has degree `4`** (in particular `\ge 3`, so there are no
degree-`2` "subdivision" points). For such graphs, a homeomorphism of the underlying topological spaces must
carry branch points (points of local degree `\ge 3`) to branch points and arcs to arcs, so **homeomorphism
coincides with graph isomorphism** (loops and multi-edges included). Now read off invariants preserved by
homeomorphism:

- **Number of connected components:** `Y_1` has `3`, `Y_2` has `2`, `Y_3` and `Y_4` have `1`. This separates
  `Y_1, Y_2` from each other and from `\{Y_3, Y_4\}`.
- **Number of loops** (edges joining a vertex to itself): `Y_3` has `3`, `Y_4` has `0`. This separates the
  two connected covers `Y_3` and `Y_4`.

Hence `Y_1, Y_2, Y_3, Y_4` are **pairwise non-homeomorphic** `3`-fold coverings of `X`. ∎

**Remark.** The instructive point is that the *homotopy* invariants are all blind here: every `3`-fold cover
has `\chi = -3`, and each connected one is `\bigvee^4 S^1` up to homotopy (its `\pi_1` is the free group of
rank `1-\chi = 4`, an index-`3` subgroup of `F_2`, free of rank `1 + 3(2-1) = 4` by Nielsen–Schreier). To
*separate* covers one must descend to homeomorphism type — components and the loop/multi-edge pattern of the
`4`-valent graph. (Connected `3`-fold covers correspond to transitive `(\sigma_a,\sigma_b)`; varying the
cycle types of the two permutations produces still more homeomorphism types, e.g. `((1\,2\,3),(1\,2))` with
one transposition gives yet another graph — there are several, of which `Y_3` and `Y_4` are two.)

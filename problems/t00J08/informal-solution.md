<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t00J08: Which ranks n let a free group have a finite-index subgroup of rank 7 — the Schreier index formula

## Why It's Hard

The problem looks like a quick plug-in to the **Nielsen–Schreier index formula** `\operatorname{rank}(G) =
1 + [F:G](n-1)` — but it explicitly forbids using "facts about free groups without justification," which is
exactly that formula and the prior fact that *subgroups of free groups are free*. So the real task is to
**prove the machinery from scratch**, and the cleanest route is topological:

- A free group is the fundamental group of a **graph** (a wedge of circles), and a subgroup corresponds to a
  **covering space**, which is again a graph. One must know/prove that (i) the fundamental group of a
  connected graph is free of rank `1 - \chi` (collapse a spanning tree), giving Nielsen–Schreier for free,
  and (ii) Euler characteristic multiplies under finite covers, giving the index formula.
- Only after building this does the arithmetic appear, and it has a subtlety: the equation `[F:G](n-1) = 6`
  is over **positive integers** with the index `[F:G] \ge 1`, and the case `n = 1` (where `F = \mathbb Z`)
  must be excluded by hand — it makes the left side `0`, never `6`, matching the fact that `\mathbb Z` has
  no rank-7 subgroup. Forgetting that `(n-1)` must be a *positive divisor of 6* (not just any factor), or
  forgetting to check each candidate is actually realizable, are the traps.

## The Key Insight

Model `F = \pi_1` of `W_n`, the wedge of `n` circles — a graph with one vertex, `n` edges, Euler
characteristic `\chi(W_n) = 1 - n`. A finite-index subgroup `G \le F` of index `k` is `\pi_1` of a connected
`k`-sheeted covering graph `\widetilde W`, so
$$
\chi(\widetilde W) = k\,\chi(W_n) = k(1-n), \qquad \operatorname{rank}(G) = 1 - \chi(\widetilde W) = 1 + k(n-1).
$$
Setting `\operatorname{rank}(G) = 7` gives `k(n-1) = 6` with `k \ge 1`, `n \ge 1`. The positive-divisor
factorizations of `6` are `(n-1, k) \in \{(1,6),(2,3),(3,2),(6,1)\}`, so
$$
\boxed{\,n \in \{2, 3, 4, 7\}\,}
$$
(and `n=1` is impossible, since then `\mathbb Z` has only rank-`\le 1` subgroups).

## Complete Proof

Throughout, "`G` contains 7 free generators" means `G` is **free of rank 7** — justified because (as proved
below) every subgroup of a free group is free, so the subgroup `G` is free, and being free on `7`
generators means rank `7`. Let `F` be free of rank `n` and `G \le F` of finite index `k := [F:G]`.

### Step 1: free groups as graphs; subgroups as coverings

Let `W_n` be the wedge of `n` circles: a graph (1-dimensional CW complex) with a single vertex `v` and `n`
edge-loops. Its fundamental group is free on the `n` loops, `\pi_1(W_n) \cong F`. Its Euler characteristic
is
$$
\chi(W_n) = \#\text{vertices} - \#\text{edges} = 1 - n .
$$
`W_n` is connected, locally path-connected, and semilocally simply connected, so covering-space theory
applies: subgroups of `\pi_1(W_n) = F` correspond to connected coverings. Let `q : \widetilde W \to W_n` be
the connected covering with `q_*(\pi_1(\widetilde W)) = G`. Its number of sheets equals the index `[F:G] =
k`.

### Step 2: a covering of a graph is a graph, and `\chi` multiplies

Because `q` is a local homeomorphism, the cell structure of `W_n` lifts: each vertex of `W_n` has exactly
`k` preimages and each (open) edge has exactly `k` preimages, each mapped homeomorphically. Hence
`\widetilde W` is again a graph, with `k\cdot 1` vertices and `k\cdot n` edges, so
$$
\chi(\widetilde W) = k\cdot 1 - k\cdot n = k(1 - n) = k\,\chi(W_n).
$$
(This is the multiplicativity of Euler characteristic under a `k`-fold covering, here proved directly by
counting lifted cells.)

### Step 3: the fundamental group of a connected graph is free of rank `1 - \chi` (Nielsen–Schreier)

Let `\Gamma` be any connected graph with `V` vertices and `E` edges, so `\chi(\Gamma) = V - E`. Choose a
**spanning tree** `T \subseteq \Gamma` (a maximal subtree; it contains all `V` vertices and `V - 1` edges,
and is contractible). Collapsing `T` to a point is a homotopy equivalence (collapsing a contractible
subcomplex), and the quotient `\Gamma / T` is a wedge of the remaining `E - (V-1)` edges — a wedge of
$$
r := E - V + 1 = 1 - \chi(\Gamma)
$$
circles. Therefore
$$
\pi_1(\Gamma) \cong \pi_1(\Gamma/T) \cong \pi_1\big(W_r\big) = \text{free group of rank } r = 1 - \chi(\Gamma).
$$
In particular `\pi_1` of *any* connected graph is **free**. Applied to the covering graph `\widetilde W`
(whose `\pi_1 \cong G`), this proves `G` is free — i.e. **Nielsen–Schreier**: every (here finite-index)
subgroup of a free group is free.

### Step 4: the index formula and the rank-7 condition

Combine Steps 2 and 3 applied to `\widetilde W`:
$$
\operatorname{rank}(G) = 1 - \chi(\widetilde W) = 1 - k(1-n) = 1 + k(n-1). \tag{Schreier}
$$
Impose `\operatorname{rank}(G) = 7`:
$$
7 = 1 + k(n-1) \quad\Longleftrightarrow\quad k(n-1) = 6,
$$
where `k = [F:G] \ge 1` is a positive integer and `n \ge 1` is the rank of `F`.

**The case `n = 1`.** Then `F \cong \mathbb Z` and `k(n-1) = k\cdot 0 = 0 \ne 6`; equivalently, every
subgroup of `\mathbb Z` is `\{0\}` or `\cong \mathbb Z` (rank `\le 1`), so it can never be free of rank `7`.
Thus `n = 1` is impossible.

**The case `n \ge 2`.** Then `n - 1 \ge 1` is a positive integer, and `k \ge 1`, so `k(n-1) = 6` forces
`n-1` to be a **positive divisor of `6`**:
$$
n - 1 \in \{1, 2, 3, 6\} \quad\Longrightarrow\quad n \in \{2, 3, 4, 7\}, \qquad k = \tfrac{6}{n-1} \in \{6, 3, 2, 1\}.
$$

**Each candidate is realizable.** For `n \ge 1`, `F` admits a subgroup of any prescribed finite index `k`:
the surjection `F \twoheadrightarrow \mathbb Z` (send one generator to `1`, the rest to `0`) pulls back the
index-`k` subgroup `k\mathbb Z \le \mathbb Z` to an index-`k` subgroup of `F`. By the Schreier formula every
index-`k` subgroup of `F` *automatically* has rank `1 + k(n-1)`, which equals `7` for the pairs above.
Concretely:

| `n` | index `k = [F:G]` | `\operatorname{rank}(G) = 1 + k(n-1)` |
|----:|:----------------:|:-------------------------------------:|
| `2` | `6`              | `1 + 6\cdot 1 = 7`                    |
| `3` | `3`              | `1 + 3\cdot 2 = 7`                    |
| `4` | `2`              | `1 + 2\cdot 3 = 7`                    |
| `7` | `1`              | `1 + 1\cdot 6 = 7`  (take `G = F`)    |

**Conclusion.** The possible ranks of `F` are exactly
$$
\boxed{\,n \in \{2,\,3,\,4,\,7\}\,}. \qquad \blacksquare
$$

**Remark.** Everything rested on one identity, the multiplicativity of Euler characteristic under finite
covers, packaged for graphs as the **Schreier index formula** `\operatorname{rank}(G) - 1 = [F:G]\,(n-1)`,
i.e. *`(\operatorname{rank}-1)` is multiplicative*. The number `7-1 = 6` must split as `[F:G]\cdot(n-1)`,
and the four factorizations of `6` are the four answers. The forbidden `n=1` corresponds to the flat case
`\chi = 0` (`\mathbb Z`), where covers never increase rank — the same Euler-characteristic obstruction that
forbids the torus from finitely covering a higher-genus surface.

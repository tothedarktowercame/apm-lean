<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J02: Grid-interval count b(N)/N converges to the Lebesgue measure of a closed set

## Why It's Hard

The quantity b(N)/N is **combinatorial** — it counts how many of the N equal grid cells of [0,1] touch A — but the target m(A) is **measure-theoretic**. The bridge is that the selected cells form a closed set U_N ⊇ A whose measure is exactly b(N)/N, so the problem becomes "show this cover shrinks down to A in measure." Two things make that delicate:

- **U_N is not monotone in N**, and it always overshoots A (a cell counts even if it meets A in a single point), so you cannot just take a decreasing-set limit of the U_N themselves.
- **Closedness of A is essential, not decorative.** If A = ℚ ∩ [0,1] (not closed), then A is dense, so *every* grid cell meets A, giving b(N) = N and b(N)/N = 1 for all N, while m(A) = 0. So any correct proof must use closedness somewhere — and the natural place is that the closed neighborhoods of A collapse onto A.

The lower bound m(A) ≤ b(N)/N is immediate; the real content is the upper bound, controlling the overhang.

## The Key Insight

Squeeze b(N)/N between two measures that both converge to m(A).

- **Lower bound.** The N grid cells cover [0,1] ⊇ A, so every point of A lies in a counted cell: A ⊆ U_N. Hence m(A) ≤ m(U_N) = b(N)/N.
- **Upper bound.** A counted cell has length 1/N and contains a point of A, so *every* point of it is within 1/N of A. Thus U_N ⊆ A_{1/N} := {x : dist(x, A) ≤ 1/N}, the closed 1/N-neighborhood, giving b(N)/N = m(U_N) ≤ m(A_{1/N}).

Because A is **closed**, the neighborhoods A_{1/N} decrease to exactly A, and by continuity of measure from above m(A_{1/N}) → m(A). The two bounds pinch b(N)/N onto m(A).

## Complete Proof

**Setup.** For N ≥ 1 partition [0,1] into the N closed cells

$$I_n^N = \left[\tfrac{n-1}{N}, \tfrac{n}{N}\right], \qquad n = 1, \dots, N,$$

each of length 1/N. Let S_N = { n : I_n^N ∩ A ≠ ∅ }, so b(N) = |S_N|, and let

$$U_N = \bigcup_{n \in S_N} I_n^N$$

be the union of the counted cells. Since A ⊆ [0,1] is closed it is compact, hence Borel, hence Lebesgue measurable, so m(A) is defined; and U_N, being a finite union of closed intervals, is measurable.

**Step 1: m(U_N) = b(N)/N.** Distinct cells I_n^N intersect only in shared endpoints, a finite set of measure zero, so they have pairwise disjoint interiors. The measure of a finite union of intervals with pairwise disjoint interiors is the sum of their lengths:

$$m(U_N) = \sum_{n \in S_N} m(I_n^N) = b(N) \cdot \tfrac{1}{N} = \tfrac{b(N)}{N}.$$

**Step 2: A ⊆ U_N, hence m(A) ≤ b(N)/N.** The cells I_1^N, …, I_N^N cover [0,1] ⊇ A. Given a ∈ A, choose n with a ∈ I_n^N; then I_n^N ∩ A ∋ a, so n ∈ S_N and a ∈ U_N. Thus A ⊆ U_N, and by monotonicity of measure,

$$m(A) \leq m(U_N) = \tfrac{b(N)}{N} \qquad \text{for every } N. \tag{1}$$

**Step 3: U_N ⊆ A_{1/N}, hence b(N)/N ≤ m(A_{1/N}).** Define the closed neighborhood

$$A_{1/N} = \{ x \in \mathbb{R} : \operatorname{dist}(x, A) \leq \tfrac{1}{N} \},$$

which is closed because x ↦ dist(x, A) is continuous. Fix n ∈ S_N and a point p ∈ I_n^N ∩ A. For any x ∈ I_n^N, since x and p both lie in an interval of length 1/N,

$$\operatorname{dist}(x, A) \leq |x - p| \leq \tfrac{1}{N},$$

so x ∈ A_{1/N}. Hence I_n^N ⊆ A_{1/N} for each n ∈ S_N, so U_N ⊆ A_{1/N}, and

$$\tfrac{b(N)}{N} = m(U_N) \leq m(A_{1/N}). \tag{2}$$

**Step 4: m(A_{1/N}) → m(A).** The sets A_{1/N} are nested decreasing: if M ≥ N then 1/M ≤ 1/N, so A_{1/M} ⊆ A_{1/N}. Their intersection is

$$\bigcap_{N=1}^{\infty} A_{1/N} = \{ x : \operatorname{dist}(x, A) \leq \tfrac{1}{N} \text{ for all } N \} = \{ x : \operatorname{dist}(x, A) = 0 \} = \overline{A} = A,$$

using that A is closed in the last equality. Moreover A_{1} = {x : dist(x, A) ≤ 1} ⊆ [-1, 2] (as A ⊆ [0,1]), so m(A_1) ≤ 3 < ∞. Continuity of measure from above (valid because the chain starts at finite measure) gives

$$\lim_{N \to \infty} m(A_{1/N}) = m\!\left( \bigcap_{N} A_{1/N} \right) = m(A). \tag{3}$$

**Step 5: squeeze.** Combining (1), (2), (3),

$$m(A) \;\leq\; \tfrac{b(N)}{N} \;\leq\; m(A_{1/N}) \;\xrightarrow[N \to \infty]{}\; m(A).$$

By the squeeze theorem the middle term converges:

$$\lim_{N \to \infty} \tfrac{b(N)}{N} = m(A). \qquad \blacksquare$$

## What Connects

**Within analysis**: This is the one-dimensional Minkowski-content / "box-counting" statement made exact — for a *measurable* set the box count overestimates measure, and the gap is governed by the measure of the ε-neighborhood. Closedness is exactly what forces the Minkowski outer content down to the Lebesgue measure here; the dense-rationals example in *Why It's Hard* is the standard witness that the hypothesis cannot be dropped.

**The load-bearing tools**: (i) the closed ε-neighborhoods of a closed set decrease to the set, and (ii) continuity of measure from above on a finite-measure chain. Both are the workhorses behind "outer approximations collapse to a closed set," and the same two facts prove regularity of Lebesgue measure on compacta.

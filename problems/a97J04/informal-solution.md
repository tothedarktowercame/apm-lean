<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J04: A continuous BV function that is AC on every [δ,1] is AC on [0,1]

## Why It's Hard

Absolute continuity on each interval `[δ,1]` is purely *local* information about the
open interval `(0,1]`, and it can degenerate as `δ → 0`: the AC modulus (the `δ_AC`
that the definition produces for a given `ε` on `[δ,1]`) is allowed to shrink to `0`
as `δ → 0`, so there is no "limiting" AC estimate to read off directly. The whole
difficulty is at the single endpoint `0`.

Continuity alone cannot close the gap. The standard cautionary example is
`f(x) = x·sin(1/x)` with `f(0)=0`: it is continuous on `[0,1]` and `C¹` (hence AC) on
every `[δ,1]` with `δ>0`, yet it is **not** absolutely continuous on `[0,1]` — because
it oscillates with infinite total variation near `0`. So the bounded-variation
hypothesis is not decoration: it must do real work, and a correct proof has to show
*exactly* how `BV` together with continuity at `0` tames the endpoint. The technical
obstacle is gluing a single global `ε`–`δ` estimate out of the local ones while
controlling the test intervals that crowd toward `0`.

## The Key Insight

Bounded variation gives a finite, nondecreasing **variation function**
`V(x) = V(f;[0,x])`. Two facts about it carry the proof:

1. **Continuity at `0` forces `V(x) → 0` as `x → 0⁺`.** Intuitively, if the variation
   did not vanish near `0`, `f` would have to wiggle by a fixed positive amount in
   every neighbourhood of `0`, contradicting continuity there. So the total
   oscillation of `f` across *any* family of intervals packed into a small `[0,a₀]`
   is at most `V(f;[0,a₀])`, which we can drive below `ε/2`.

2. Everything else lives in `[a₀,1]`, where absolute continuity is a **hypothesis**.

The clean way to combine them is a splitting trick: if a test interval straddles the
cut point `a₀`, cut it *at* `a₀`. By the triangle inequality this only increases the
oscillation sum, and afterwards every interval lies entirely in `[0,a₀]` (controlled
by the variation) or entirely in `[a₀,1]` (controlled by AC there). No interval is
left straddling, which is exactly the case that makes the naive split awkward.

## Complete Proof

**Definitions.** `f` is *absolutely continuous* on `[a,b]` if for every `ε>0` there is
`δ>0` such that for every finite family of non-overlapping subintervals
`(a_1,b_1),…,(a_n,b_n)` of `[a,b]` with `∑_i (b_i − a_i) < δ`, one has
`∑_i |f(b_i) − f(a_i)| < ε`.

For `0 ≤ x ≤ 1` let

$$V(x) \;=\; V(f;[0,x]) \;=\; \sup \sum_{j=1}^{m} |f(t_j) - f(t_{j-1})|,$$

the supremum over all partitions `0 = t_0 < t_1 < … < t_m = x`. Since `f` is of
bounded variation on `[0,1]`, `V(1) < ∞`. The function `V` is nondecreasing, `V(0)=0`,
and variation is **additive**: `V(1) = V(f;[0,c]) + V(f;[c,1])` for every `c∈[0,1]`.

---

**Lemma 1 (the variation vanishes at the endpoint).** `V(x) → 0` as `x → 0⁺`.

*Proof.* Fix `ε>0`. By definition of `V(1)` as a supremum, choose a partition
`0=t_0<t_1<…<t_m=1` of `[0,1]` whose variation sum satisfies

$$\sum_{j=1}^{m} |f(t_j)-f(t_{j-1})| \;>\; V(1) - \tfrac{\varepsilon}{2}.$$

By continuity of `f` at `0`, choose `a₀` with `0 < a₀ < t_1` and `|f(a₀)-f(0)| < ε/2`.
Consider the partition `a₀ < t_1 < … < t_m = 1` of `[a₀,1]`. Using
`|f(t_1)-f(a₀)| ≥ |f(t_1)-f(0)| - |f(0)-f(a₀)|`,

$$
V(f;[a₀,1]) \;\ge\; |f(t_1)-f(a₀)| + \sum_{j=2}^{m}|f(t_j)-f(t_{j-1})|
\;\ge\; \Big(\sum_{j=1}^{m}|f(t_j)-f(t_{j-1})|\Big) - |f(0)-f(a₀)|
\;>\; \big(V(1)-\tfrac{\varepsilon}{2}\big) - \tfrac{\varepsilon}{2}.
$$

So `V(f;[a₀,1]) > V(1) - ε`, and by additivity
`V(f;[0,a₀]) = V(1) - V(f;[a₀,1]) < ε`. Since `V` is nondecreasing, `V(x) ≤ V(a₀) < ε`
for all `0 ≤ x ≤ a₀`. As `ε>0` was arbitrary, `V(x) → 0` as `x → 0⁺`. ∎

---

**Lemma 2 (oscillation is bounded by variation).** For any finite family of
non-overlapping intervals `(a_i,b_i) ⊆ [0,c]`,
`∑_i |f(b_i)-f(a_i)| ≤ V(f;[0,c])`.

*Proof.* Order the endpoints; the points `{a_i, b_i}` are a subset of a partition of
`[0,c]`, and inserting the missing partition points only adds non-negative terms to
the sum `∑|Δf|`. Hence `∑_i |f(b_i)-f(a_i)|` is at most the supremum defining
`V(f;[0,c])`. ∎

---

**Theorem.** `f` is absolutely continuous on `[0,1]`.

*Proof.* Let `ε>0`.

*Step 1 — choose the cut point.* By Lemma 1 pick `a₀ ∈ (0,1)` with
`V(f;[0,a₀]) < ε/2`.

*Step 2 — use AC on `[a₀,1]`.* Since `0 < a₀ < 1`, the hypothesis gives that `f` is
absolutely continuous on `[a₀,1]`: there is `δ > 0` such that for non-overlapping
intervals in `[a₀,1]` of total length `< δ`, the oscillation sum is `< ε/2`.

*Step 3 — the test family.* Let `(a_1,b_1),…,(a_n,b_n)` be non-overlapping
subintervals of `[0,1]` with `∑_i (b_i - a_i) < δ`. For any interval that straddles
`a₀` (i.e. `a_i < a₀ < b_i`), replace it by the two intervals `(a_i,a₀)` and
`(a₀,b_i)`. This keeps the family non-overlapping, preserves the total length (so it
is still `< δ`), and by the triangle inequality
`|f(b_i)-f(a_i)| ≤ |f(a₀)-f(a_i)| + |f(b_i)-f(a₀)|` it does **not decrease** the
oscillation sum. After this refinement every interval lies entirely in `[0,a₀]` or
entirely in `[a₀,1]`. Split the family accordingly into `A` and `B`.

*Step 4 — bound each group.*

- Group `A` (intervals `⊆ [0,a₀]`): by Lemma 2,
  `∑_{A} |f(b_i)-f(a_i)| ≤ V(f;[0,a₀]) < ε/2`.
- Group `B` (intervals `⊆ [a₀,1]`): their total length is `≤ ∑_i (b_i-a_i) < δ`, so by
  Step 2, `∑_{B} |f(b_i)-f(a_i)| < ε/2`.

*Step 5 — conclude.* The refined oscillation sum is `< ε/2 + ε/2 = ε`. Because
refining (splitting at `a₀`) only increased the sum, the **original** sum
`∑_i |f(b_i)-f(a_i)|` is also `< ε`.

Thus the chosen `δ` witnesses the absolute-continuity condition for this `ε`. Since
`ε>0` was arbitrary, `f` is absolutely continuous on `[0,1]`. ∎

---

**Where each hypothesis is used.** *Bounded variation* makes `V(1) < ∞`, so the
variation function exists and Lemma 1/Lemma 2 have content. *Continuity at `0`* is the
engine of Lemma 1 (`V(x) → 0`); it is the precise ingredient that the bare
counterexample `x·sin(1/x)` lacks in spirit (there it is `BV` that fails, but the moral
is the same — without endpoint control the variation does not vanish). *Absolute
continuity on `[a₀,1]`* handles the bulk of the interval in Step 2. Drop any one of the
three and the conclusion fails.

**Alternative viewpoint (FTC).** One can also argue via the integral: `BV` gives
`f' ∈ L¹[0,1]` with `∫_0^1 |f'| ≤ V(1)`; AC on `[δ,1]` gives
`f(x)-f(δ) = ∫_δ^x f'`; letting `δ→0⁺`, continuity sends `f(δ)→f(0)` and absolute
continuity of the Lebesgue integral sends `∫_δ^x f' → ∫_0^x f'`, so
`f(x) = f(0) + ∫_0^x f'`. An indefinite integral of an `L¹` function is absolutely
continuous, hence so is `f`. This is the same three hypotheses doing the same three
jobs, packaged through the Fundamental Theorem of Calculus.

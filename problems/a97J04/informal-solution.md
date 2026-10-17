<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a97J04: A continuous BV function that is AC on every $[\delta,1]$ is AC on $[0,1]$

## Why It's Hard

Absolute continuity on each interval $[\delta,1]$ is purely *local* information about the
open interval $(0,1]$, and it can degenerate as $\delta \to 0$: the AC modulus (the $\delta_{AC}$
that the definition produces for a given $\varepsilon$ on $[\delta,1]$) is allowed to shrink to $0$
as $\delta \to 0$, so there is no "limiting" AC estimate to read off directly. The whole
difficulty is at the single endpoint $0$.

Continuity alone cannot close the gap. The standard cautionary example is
$f(x) = x \cdot \sin(1/x)$ with $f(0)=0$: it is continuous on $[0,1]$ and $C^{1}$ (hence AC) on
every $[\delta,1]$ with $\delta>0$, yet it is **not** absolutely continuous on $[0,1]$ — because
it oscillates with infinite total variation near $0$. So the bounded-variation
hypothesis is not decoration: it must do real work, and a correct proof has to show
*exactly* how $BV$ together with continuity at $0$ tames the endpoint. The technical
obstacle is gluing a single global $\varepsilon$–$\delta$ estimate out of the local ones while
controlling the test intervals that crowd toward $0$.

## The Key Insight

Bounded variation gives a finite, nondecreasing **variation function**
$V(x) = V(f;[0,x])$. Two facts about it carry the proof:

1. **Continuity at $0$ forces $V(x) \to 0$ as $x \to 0^{+}$.** Intuitively, if the variation
   did not vanish near $0$, $f$ would have to wiggle by a fixed positive amount in
   every neighbourhood of $0$, contradicting continuity there. So the total
   oscillation of $f$ across *any* family of intervals packed into a small $[0,a_{0}]$
   is at most $V(f;[0,a_{0}])$, which we can drive below $\varepsilon/2$.

2. Everything else lives in $[a_{0},1]$, where absolute continuity is a **hypothesis**.

The clean way to combine them is a splitting trick: if a test interval straddles the
cut point $a_{0}$, cut it *at* $a_{0}$. By the triangle inequality this only increases the
oscillation sum, and afterwards every interval lies entirely in $[0,a_{0}]$ (controlled
by the variation) or entirely in $[a_{0},1]$ (controlled by AC there). No interval is
left straddling, which is exactly the case that makes the naive split awkward.

## Complete Proof

**Definitions.** $f$ is *absolutely continuous* on $[a,b]$ if for every $\varepsilon>0$ there is
$\delta>0$ such that for every finite family of non-overlapping subintervals
$(a_1,b_1),\ldots,(a_n,b_n)$ of $[a,b]$ with $\sum_i (b_i - a_i) < \delta$, one has
$\sum_i |f(b_i) - f(a_i)| < \varepsilon$.

For $0 \leq x \leq 1$ let

$$V(x) \;=\; V(f;[0,x]) \;=\; \sup \sum_{j=1}^{m} |f(t_j) - f(t_{j-1})|,$$

the supremum over all partitions $0 = t_0 < t_1 < \ldots < t_m = x$. Since $f$ is of
bounded variation on $[0,1]$, $V(1) < \infty$. The function $V$ is nondecreasing, $V(0)=0$,
and variation is **additive**: $V(1) = V(f;[0,c]) + V(f;[c,1])$ for every $c\in[0,1]$.

---

**Lemma 1 (the variation vanishes at the endpoint).** $V(x) \to 0$ as $x \to 0^{+}$.

*Proof.* Fix $\varepsilon>0$. By definition of $V(1)$ as a supremum, choose a partition
$0=t_0<t_1<\ldots<t_m=1$ of $[0,1]$ whose variation sum satisfies

$$\sum_{j=1}^{m} |f(t_j)-f(t_{j-1})| \;>\; V(1) - \tfrac{\varepsilon}{2}.$$

By continuity of $f$ at $0$, choose $a_{0}$ with $0 < a_{0} < t_1$ and $|f(a_{0})-f(0)| < \varepsilon/2$.
Consider the partition $a_{0} < t_1 < \ldots < t_m = 1$ of $[a_{0},1]$. Using
$|f(t_1)-f(a_{0})| \geq |f(t_1)-f(0)| - |f(0)-f(a_{0})|$,

$$
V(f;[a₀,1]) \;\ge\; |f(t_1)-f(a₀)| + \sum_{j=2}^{m}|f(t_j)-f(t_{j-1})|
\;\ge\; \Big(\sum_{j=1}^{m}|f(t_j)-f(t_{j-1})|\Big) - |f(0)-f(a₀)|
\;>\; \big(V(1)-\tfrac{\varepsilon}{2}\big) - \tfrac{\varepsilon}{2}.
$$

So $V(f;[a_{0},1]) > V(1) - \varepsilon$, and by additivity
$V(f;[0,a_{0}]) = V(1) - V(f;[a_{0},1]) < \varepsilon$. Since $V$ is nondecreasing, $V(x) \leq V(a_{0}) < \varepsilon$
for all $0 \leq x \leq a_{0}$. As $\varepsilon>0$ was arbitrary, $V(x) \to 0$ as $x \to 0^{+}$. ∎

---

**Lemma 2 (oscillation is bounded by variation).** For any finite family of
non-overlapping intervals $(a_i,b_i) \subseteq [0,c]$,
$\sum_i |f(b_i)-f(a_i)| \leq V(f;[0,c])$.

*Proof.* Order the endpoints; the points $\{a_i, b_i\}$ are a subset of a partition of
$[0,c]$, and inserting the missing partition points only adds non-negative terms to
the sum $\sum|\Delta f|$. Hence $\sum_i |f(b_i)-f(a_i)|$ is at most the supremum defining
$V(f;[0,c])$. ∎

---

**Theorem.** $f$ is absolutely continuous on $[0,1]$.

*Proof.* Let $\varepsilon>0$.

*Step 1 — choose the cut point.* By Lemma 1 pick $a_{0} \in (0,1)$ with
$V(f;[0,a_{0}]) < \varepsilon/2$.

*Step 2 — use AC on $[a_{0},1]$.* Since $0 < a_{0} < 1$, the hypothesis gives that $f$ is
absolutely continuous on $[a_{0},1]$: there is $\delta > 0$ such that for non-overlapping
intervals in $[a_{0},1]$ of total length $< \delta$, the oscillation sum is $< \varepsilon/2$.

*Step 3 — the test family.* Let $(a_1,b_1),\ldots,(a_n,b_n)$ be non-overlapping
subintervals of $[0,1]$ with $\sum_i (b_i - a_i) < \delta$. For any interval that straddles
$a_{0}$ (i.e. $a_i < a_{0} < b_i$), replace it by the two intervals $(a_i,a_{0})$ and
$(a_{0},b_i)$. This keeps the family non-overlapping, preserves the total length (so it
is still $< \delta$), and by the triangle inequality
$|f(b_i)-f(a_i)| \leq |f(a_{0})-f(a_i)| + |f(b_i)-f(a_{0})|$ it does **not decrease** the
oscillation sum. After this refinement every interval lies entirely in $[0,a_{0}]$ or
entirely in $[a_{0},1]$. Split the family accordingly into $A$ and $B$.

*Step 4 — bound each group.*

- Group $A$ (intervals $\subseteq [0,a_{0}]$): by Lemma 2,
  $\sum_{A} |f(b_i)-f(a_i)| \leq V(f;[0,a_{0}]) < \varepsilon/2$.
- Group $B$ (intervals $\subseteq [a_{0},1]$): their total length is $\leq \sum_i (b_i-a_i) < \delta$, so by
  Step 2, $\sum_{B} |f(b_i)-f(a_i)| < \varepsilon/2$.

*Step 5 — conclude.* The refined oscillation sum is $< \varepsilon/2 + \varepsilon/2 = \varepsilon$. Because
refining (splitting at $a_{0}$) only increased the sum, the **original** sum
$\sum_i |f(b_i)-f(a_i)|$ is also $< \varepsilon$.

Thus the chosen $\delta$ witnesses the absolute-continuity condition for this $\varepsilon$. Since
$\varepsilon>0$ was arbitrary, $f$ is absolutely continuous on $[0,1]$. ∎

---

**Where each hypothesis is used.** *Bounded variation* makes $V(1) < \infty$, so the
variation function exists and Lemma 1/Lemma 2 have content. *Continuity at $0$* is the
engine of Lemma 1 ($V(x) \to 0$); it is the precise ingredient that the bare
counterexample $x \cdot \sin(1/x)$ lacks in spirit (there it is $BV$ that fails, but the moral
is the same — without endpoint control the variation does not vanish). *Absolute
continuity on $[a_{0},1]$* handles the bulk of the interval in Step 2. Drop any one of the
three and the conclusion fails.

**Alternative viewpoint (FTC).** One can also argue via the integral: $BV$ gives
$f' \in L^{1}[0,1]$ with $\int_0^1 |f'| \leq V(1)$; AC on $[\delta,1]$ gives
$f(x)-f(\delta) = \int_\delta^x f'$; letting $\delta\to0^{+}$, continuity sends $f(\delta)\to f(0)$ and absolute
continuity of the Lebesgue integral sends $\int_\delta^x f' \to \int_0^x f'$, so
$f(x) = f(0) + \int_0^x f'$. An indefinite integral of an $L^{1}$ function is absolutely
continuous, hence so is $f$. This is the same three hypotheses doing the same three
jobs, packaged through the Fundamental Theorem of Calculus.

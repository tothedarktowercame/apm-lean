<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a98J01: Lusin's theorem — measurable functions are "almost" continuous

## Why It's Hard

Lusin's theorem makes a claim that is, on first hearing, hard to believe. A
measurable function can be discontinuous *everywhere*: the Dirichlet function
$\mathbf 1_{\mathbb Q}$ on $[0,1]$ is measurable yet has no point of continuity at
all. Lusin nevertheless asserts that after deleting a set of arbitrarily small
measure, what remains is a set on which the function is genuinely continuous. The
tension is that "measurable" is defined purely in terms of preimages of open sets
being measurable — a statement with no a priori topological/continuity content — and
the theorem extracts honest continuity from it.

Two things make the proof delicate rather than routine:

1. **The right reading of the conclusion.** "$f$ restricted to the closed set $K$ is
   continuous" means continuity in the *relative* (subspace) topology of $K$ — not
   that $f$, viewed on all of $[a,b]$, is continuous at the points of $K$. For
   $\mathbf 1_{\mathbb Q}$ one deletes a small open neighborhood of the rationals and
   is left with a compact set of irrationals on which the function is identically
   $0$, hence continuous *as a function on that set*. Conflating the two readings
   makes the theorem look false.

2. **Assembling the machinery and budgeting the error.** No single tool does it. One
   needs (a) the inner regularity of Lebesgue measure to manufacture compact sets,
   (b) the fact that finitely many disjoint compact sets are mutually separated, (c)
   Egorov's theorem to turn pointwise convergence into uniform convergence on a
   large set, and (d) the theorem that a uniform limit of continuous functions is
   continuous. These must be combined while spending only a total of $\varepsilon$
   measure across *infinitely many* approximation steps — handled by a geometric
   $\varepsilon/2^n$ budget.

## The Key Insight

Factor the problem through simple functions:

- A finite-valued measurable $f$ is the **pointwise limit of simple functions**
  $s_n$.
- Each **simple function is continuous off a small set**: by inner regularity each of
  its finitely many level sets contains a compact set capturing all but a sliver of
  its measure, and finitely many *disjoint compact* sets sit at positive distance
  from one another — so a function that is constant on each is continuous on their
  union.
- **Egorov** upgrades $s_n \to f$ from pointwise to *uniform* on a set of nearly full
  measure.
- A **uniform limit of continuous functions is continuous**.

Intersect the (compact) good sets for all the $s_n$ with Egorov's uniform-convergence
set, spending $\varepsilon/2^{\,n+1}$ on the $n$-th and $\varepsilon/2$ on Egorov.
On the resulting compact $K$ every $s_n|_K$ is continuous and $s_n \to f$ uniformly,
so $f|_K$ is continuous — while $m([a,b]\setminus K) < \varepsilon$.

## Complete Proof

**Theorem (Lusin).** Let $f:[a,b]\to\R$ be Lebesgue measurable and finite almost
everywhere. Then for every $\varepsilon > 0$ there is a compact set
$K \subseteq [a,b]$ with
$$m\big([a,b]\setminus K\big) < \varepsilon$$
such that the restriction $f|_K$ is continuous. Equivalently, there is a continuous
function $g:[a,b]\to\R$ with $m\{x : f(x)\neq g(x)\} < \varepsilon$, and one may
arrange $\sup_{[a,b]}|g| \le \operatorname{ess\,sup}|f|$.

**Reduction.** The set $\{x : |f(x)| = \infty\}$ is null; redefining $f$ to be $0$
there changes it on a null set and affects neither hypothesis nor conclusion. So
assume $f$ is finite-valued on all of $[a,b]$.

---

**Step 1 — Simple functions are continuous off a small set.**
Let $s = \sum_{k=1}^{m} c_k\,\mathbf 1_{E_k}$ be simple, where the measurable sets
$E_1,\dots,E_m$ are disjoint with $\bigcup_k E_k = [a,b]$ and the $c_k$ distinct. Fix
$\delta > 0$. By inner regularity of Lebesgue measure, choose for each $k$ a compact
set $K_k \subseteq E_k$ with $m(E_k \setminus K_k) < \delta/m$. Put
$K' = \bigcup_{k=1}^m K_k$; then $K'$ is compact and
$$m\big([a,b]\setminus K'\big) = \sum_{k=1}^m m(E_k\setminus K_k) < \delta.$$
The $K_k$ are pairwise disjoint compact sets, so $\rho := \min_{j\neq k}
\operatorname{dist}(K_j, K_k) > 0$. On $K'$ the function $s$ equals the constant
$c_k$ on $K_k$; for any $x \in K_k$, every point of $K'$ within distance $\rho$ of
$x$ lies in the same $K_k$, where $s = c_k$. Hence $s|_{K'}$ is locally constant,
therefore continuous.

**Step 2 — Pointwise approximation and Egorov.**
Since $f$ is finite-valued and measurable, there is a sequence of simple functions
$s_n$ with $s_n(x) \to f(x)$ for every $x \in [a,b]$ (e.g. the standard dyadic
truncation $s_n = \sum_{j} \frac{j}{2^n}\mathbf 1_{\{j/2^n \le f < (j+1)/2^n\}}$ on
$|f|\le n$, and $s_n = \pm n$ where $\pm f > n$). Fix $\varepsilon > 0$.

- *Egorov.* As $[a,b]$ has finite measure and $s_n \to f$ pointwise (hence a.e.),
  Egorov's theorem yields a measurable set $A \subseteq [a,b]$ with
  $m([a,b]\setminus A) < \varepsilon/4$ on which $s_n \to f$ **uniformly**. By inner
  regularity pick a compact $K_0 \subseteq A$ with $m([a,b]\setminus K_0) <
  \varepsilon/2$; uniform convergence persists on the subset $K_0$.

- *Good sets for each $s_n$.* By Step 1, for each $n \ge 1$ choose a compact
  $K_n \subseteq [a,b]$ with $m([a,b]\setminus K_n) < \varepsilon/2^{\,n+1}$ such
  that $s_n|_{K_n}$ is continuous.

**Step 3 — Intersect and conclude continuity of $f|_K$.**
Let
$$K = K_0 \cap \bigcap_{n=1}^{\infty} K_n .$$
$K$ is compact (a closed subset of the compact $K_0$), and
$$m\big([a,b]\setminus K\big) \le m([a,b]\setminus K_0) + \sum_{n=1}^{\infty}
   m([a,b]\setminus K_n) < \frac{\varepsilon}{2} + \sum_{n=1}^{\infty}
   \frac{\varepsilon}{2^{\,n+1}} = \frac{\varepsilon}{2} + \frac{\varepsilon}{2}
   = \varepsilon .$$
On $K$: each $s_n|_K$ is continuous (it is the restriction of the continuous
$s_n|_{K_n}$ to $K \subseteq K_n$), and $s_n \to f$ uniformly on $K$ (since
$K \subseteq K_0 \subseteq A$). A uniform limit of continuous functions is
continuous; therefore $f|_K$ is continuous. This proves the closed-set form.

**Step 4 — The continuous-function form.**
$f|_K$ is continuous on the compact set $K \subseteq [a,b]$. The complement
$[a,b]\setminus K$ is open in $[a,b]$, i.e. a countable union of disjoint relatively
open intervals; extend $f|_K$ across each such gap by linear interpolation between
the endpoint values on $K$ (and constantly on any unbounded-type end interval
touching $a$ or $b$). This yields a continuous $g:[a,b]\to\R$ with $g = f$ on $K$ —
which is exactly the Tietze extension theorem made explicit in one dimension. Then
$$\{x : f(x)\neq g(x)\} \subseteq [a,b]\setminus K, \qquad
   m\{x : f(x)\neq g(x)\} < \varepsilon .$$
Finally, if $M = \operatorname{ess\,sup}|f|$ is finite, replace $g$ by its truncation
$\max(-M,\min(M,g))$: this is still continuous, still agrees with $f$ on $K$ (where
$|f|\le M$), and satisfies $\sup|g|\le M$. $\blacksquare$

---

**Remarks.**

- *Where each hypothesis is used.* Boundedness of the interval gives finite measure,
  which Egorov requires; closedness gives compactness of $[a,b]$ and hence of $K$.
  Inner regularity is what converts "measurable" into "compact-set" data — the one
  bridge from measure theory to topology.

- *Necessity of the small deletion.* One cannot take $\varepsilon = 0$: again
  $\mathbf 1_{\mathbb Q}$ is continuous on no set of full measure that is "too large"
  in the naive sense — the deleted set can be made arbitrarily small but not empty.

- *Sharper conclusion.* The proof gives $K$ compact, not merely closed, and $g$ can
  be taken continuous on all of $\R$ by extending it to be constant outside $[a,b]$.

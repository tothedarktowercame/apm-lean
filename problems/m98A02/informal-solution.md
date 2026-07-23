<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m98A02: Bounded = continuous, B(X,Y) is Banach, and the Neumann series

## Why It's Hard

These are the foundational facts of operator theory, and their difficulty is in the *care* required rather
than any single clever trick. Part (a) asks for three linked results: the definition of boundedness, its
equivalence with continuity, and the completeness of the operator space `B(X,Y)`. The equivalence hinges on
**linearity** — it is what lets continuity at a single point (the origin) propagate to a global Lipschitz
bound via a rescaling argument. Completeness of `B(X,Y)` is the subtle one: you must build a candidate
limit operator *pointwise* (using completeness of `Y`), then prove the convergence is actually *uniform*
in the operator norm — the classic "pointwise limit, then upgrade to uniform" pattern.

Part (b) is the **Neumann series**, the operator analogue of the geometric series `\tfrac{1}{1-a} = \sum a^n`.
The crux is realizing that `\sum_{n} A^n` *converges* — which is not automatic for an infinite series of
operators and uses precisely the completeness proved in (a), together with `\|A\| < 1` providing a
geometric majorant. The norm bounds then come from two opposite directions: the upper bound from the series
itself (triangle inequality), the lower bound from submultiplicativity of the operator norm.

## The Key Insight

- **(a)** `A` bounded means `\|Ax\| \le C\|x\|`; with linearity this is *Lipschitz*, hence continuous, and
  conversely continuity at `0` gives a `\delta`-ball on which `\|Ax\| \le 1`, which rescales to
  `\|Ax\| \le \tfrac1\delta\|x\|`. For completeness, a Cauchy `(A_n)` makes each `(A_nx)` Cauchy in the
  *complete* `Y`, defining `Ax = \lim A_n x`; one checks `A` is bounded and `A_n \to A` uniformly.
- **(b)** Since `B(X)` is complete (by (a)) and `\sum \|A^n\| \le \sum \|A\|^n = \tfrac{1}{1-\|A\|} < \infty`,
  the **Neumann series** `S = \sum_{n=0}^\infty A^n` converges, and telescoping shows `(I-A)S = S(I-A) = I`.
  Then `\|(I-A)^{-1}\| = \|\sum A^n\| \le \tfrac{1}{1-\|A\|}` (upper), and `1 = \|I\| \le \|(I-A)^{-1}\|\,\|I-A\| \le \|(I-A)^{-1}\|(1+\|A\|)`
  gives `\|(I-A)^{-1}\| \ge \tfrac{1}{1+\|A\|}` (lower).

## Complete Proof

### (a) Bounded `\Leftrightarrow` continuous, and `B(X,Y)` is Banach

**Definition.** `A : X \to Y` linear is **bounded** if there is `C \ge 0` with `\|Ax\|_Y \le C\|x\|_X` for
all `x`. The smallest such `C` is the operator norm `\|A\| = \sup_{x \ne 0}\frac{\|Ax\|}{\|x\|} = \sup_{\|x\|=1}\|Ax\|`.

**Bounded `\Rightarrow` continuous.** If `\|Ax\| \le C\|x\|`, then for any `x_0`,
`\|Ax - Ax_0\| = \|A(x - x_0)\| \le C\|x - x_0\| \to 0` as `x \to x_0`. So `A` is (Lipschitz) continuous.

**Continuous `\Rightarrow` bounded.** By linearity, continuity anywhere implies continuity at `0`. So there
is `\delta > 0` with `\|x\| \le \delta \Rightarrow \|Ax\| \le 1`. For any `x \ne 0`, set
`z = \delta x/\|x\|` (so `\|z\| = \delta`); then `\|Az\| \le 1`, i.e.
`\frac{\delta}{\|x\|}\|Ax\| \le 1`, giving `\|Ax\| \le \tfrac1\delta\|x\|`. So `A` is bounded with
`C = 1/\delta`.

**`B(X,Y)` is a normed space.** `B(X,Y)` is a vector space (sums and scalar multiples of bounded operators
are bounded), and `\|\cdot\|` is a norm: `\|A\| = 0 \iff A = 0`; `\|\lambda A\| = |\lambda|\|A\|`; and
`\|(A+B)x\| \le \|Ax\| + \|Bx\| \le (\|A\|+\|B\|)\|x\|` gives `\|A+B\| \le \|A\| + \|B\|`.

**`B(X,Y)` is complete (uses `Y` Banach).** Let `(A_n)` be Cauchy in `B(X,Y)`. For each `x`,
`\|A_n x - A_m x\| \le \|A_n - A_m\|\,\|x\| \to 0`, so `(A_n x)` is Cauchy in `Y`; since `Y` is complete it
converges, and we define `Ax = \lim_n A_n x`. Then `A` is linear (a pointwise limit of linear maps). It is
bounded: `(A_n)` Cauchy is bounded, `\|A_n\| \le M`, so `\|Ax\| = \lim_n \|A_n x\| \le M\|x\|`, giving
`\|A\| \le M`. Finally `A_n \to A` in norm: given `\varepsilon > 0`, pick `N` with `\|A_n - A_m\| < \varepsilon`
for `n,m \ge N`; for `\|x\| \le 1`, `\|A_n x - A_m x\| < \varepsilon`, and letting `m \to \infty`,
`\|A_n x - Ax\| \le \varepsilon`; taking the supremum over `\|x\| \le 1`, `\|A_n - A\| \le \varepsilon` for
`n \ge N`. So `A_n \to A` and `B(X,Y)` is a **Banach space**. ∎

### (b) The Neumann series and norm bounds

Now `A \in B(X) = B(X,X)` with `\|A\| < 1`; `I : X \to X` is the identity.

**Convergence of the Neumann series.** Consider `S = \sum_{n=0}^\infty A^n` in `B(X)`. By
submultiplicativity `\|A^n\| \le \|A\|^n`, so

$$\sum_{n=0}^\infty \|A^n\| \le \sum_{n=0}^\infty \|A\|^n = \frac{1}{1 - \|A\|} < \infty$$

(geometric, since `\|A\| < 1`). Thus the series is absolutely convergent in `B(X)`, which is **complete** by
part (a), so `S \in B(X)` is well defined.

**`S = (I-A)^{-1}`.** Telescoping the partial sums `S_N = \sum_{n=0}^N A^n`,

$$(I - A)S_N = \sum_{n=0}^N A^n - \sum_{n=1}^{N+1} A^n = I - A^{N+1},$$

and `\|A^{N+1}\| \le \|A\|^{N+1} \to 0`, so letting `N \to \infty` gives `(I-A)S = I`. Identically
`S(I-A) = I`. Hence `I - A` is invertible with `(I-A)^{-1} = S = \sum_{n=0}^\infty A^n`.

**Upper bound.** By the triangle inequality and the geometric majorant,

$$\|(I-A)^{-1}\| = \Big\|\sum_{n=0}^\infty A^n\Big\| \le \sum_{n=0}^\infty \|A\|^n = \frac{1}{1 - \|A\|}.$$

**Lower bound.** From `(I-A)^{-1}(I-A) = I` and submultiplicativity (with `\|I\| = 1`),

$$1 = \|I\| \le \|(I-A)^{-1}\|\;\|I - A\| \le \|(I-A)^{-1}\|\,(1 + \|A\|),$$

using `\|I - A\| \le \|I\| + \|A\| = 1 + \|A\|`. Therefore `\|(I-A)^{-1}\| \ge \dfrac{1}{1 + \|A\|}`.
Combining,

$$\boxed{\ \frac{1}{1 + \|A\|} \le \|(I-A)^{-1}\| \le \frac{1}{1 - \|A\|}.\ }\qquad\blacksquare$$

**Remark.** The two parts interlock: the **completeness of `B(X)`** proved in (a) is exactly the hypothesis
that makes the operator series in (b) converge — absolute convergence implies convergence only in a complete
space. The Neumann series is the operator form of `\tfrac{1}{1-a} = \sum a^n`, valid in the "unit disk"
`\|A\| < 1`, and it is the workhorse behind perturbation theory: invertibility is an *open* condition, since
any `B` with `\|B - T\| < 1/\|T^{-1}\|` is invertible by writing `B = T(I - T^{-1}(T-B))`.

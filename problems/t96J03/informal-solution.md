<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t96J03: A nonempty closed set in ℝⁿ contains a nearest point to any external point

## Why It's Hard

The distance `d=\inf_{x\in X}\|x-y_0\|` is an *infimum*, and the danger is that an infimum need not be
**attained**: a continuous function on a non-compact set can approach its infimum without reaching it (e.g.
`e^{-t}` on `[0,\infty)` never hits `0`). The set `X` is *closed* but possibly **unbounded**, hence not
compact, so the extreme value theorem does **not** apply to `X` directly. The whole difficulty is recovering
compactness.

The fix is to notice that a near-minimizer cannot be far from `y_0`: any candidate that improves on a fixed
point `x_1\in X` must lie inside a bounded ball. So one **truncates** `X` to its intersection with a closed
ball around `y_0` — a *closed and bounded*, hence (by Heine–Borel) **compact**, set with the *same* infimum
— and then the extreme value theorem attains the minimum there. The subtlety is choosing the ball so that
truncating changes neither the infimum nor membership in `X`.

## The Key Insight

Fix any `x_1\in X` and let `R=\|x_1-y_0\|`. Replace `X` by
$$
K = X\cap\overline B(y_0,R) = \{x\in X : \|x-y_0\|\le R\},
$$
which is **compact** (closed `\cap` closed ball = closed and bounded in `\mathbb R^n`) and **nonempty**
(`x_1\in K`). Points of `X` outside `K` have distance `>R\ge d`, so `\inf_K\|x-y_0\| = \inf_X\|x-y_0\| = d`.
The continuous map `x\mapsto\|x-y_0\|` attains its minimum on the compact `K` (extreme value theorem) at some
`x_0\in K\subseteq X`, giving `\|x_0-y_0\| = d\le\|x-y_0\|` for all `x\in X`.

## Complete Proof

Let `X\subseteq\mathbb R^n` be nonempty and closed, and `y_0\in\mathbb R^n` (the hypothesis `y_0\notin X` is
not needed for existence; see the remark). Define the **distance function**
$$
\varphi:\mathbb R^n\to[0,\infty), \qquad \varphi(x)=\|x-y_0\|,
$$
and `d:=\inf_{x\in X}\varphi(x)`. Since `X\ne\varnothing`, `d` is a finite real number `\ge0`. We produce
`x_0\in X` with `\varphi(x_0)=d`.

**`\varphi` is continuous.** By the reverse triangle inequality, `|\,\|x-y_0\|-\|x'-y_0\|\,|\le\|x-x'\|`, so
`\varphi` is `1`-Lipschitz, hence continuous.

**Truncate to a compact set.** Choose any point `x_1\in X` (possible since `X\ne\varnothing`) and set
`R:=\varphi(x_1)=\|x_1-y_0\|`. Define
$$
K := X\cap\overline B(y_0,R), \qquad \overline B(y_0,R)=\{x:\|x-y_0\|\le R\}.
$$
Then:

- `K` is **nonempty**, since `\varphi(x_1)=R\le R` gives `x_1\in K`.
- `K` is **closed**: an intersection of the closed set `X` with the closed ball `\overline B(y_0,R)`.
- `K` is **bounded**: `K\subseteq\overline B(y_0,R)`.

By the **Heine–Borel theorem**, a closed and bounded subset of `\mathbb R^n` is **compact**; hence `K` is
compact.

**The infimum over `X` is the infimum over `K`.** Clearly `\inf_K\varphi\ge\inf_X\varphi=d` since `K\subseteq
X`. Conversely, for any `x\in X`: if `\varphi(x)\le R` then `x\in K`, so `\varphi(x)\ge\inf_K\varphi`; and if
`\varphi(x)>R`, then `\varphi(x)>R=\varphi(x_1)\ge\inf_K\varphi`. In either case `\varphi(x)\ge\inf_K\varphi`,
so `d=\inf_X\varphi\ge\inf_K\varphi`. Therefore
$$
\inf_K\varphi = \inf_X\varphi = d .
$$

**Attain the minimum (extreme value theorem).** `\varphi` is continuous and `K` is compact, so by the
**extreme value theorem** `\varphi` attains its minimum on `K`: there is `x_0\in K` with
$$
\varphi(x_0)=\inf_K\varphi = d .
$$
Since `K\subseteq X`, we have `x_0\in X`, and for every `x\in X`,
$$
\|x_0-y_0\| = \varphi(x_0) = d = \inf_{x'\in X}\varphi(x') \le \varphi(x) = \|x-y_0\| .
$$
Thus `x_0\in X` is a nearest point of `X` to `y_0`. ∎

**Remark.** The mechanism is "truncate to restore compactness": a general closed set is not compact, so the
extreme value theorem fails on it, but the *minimizer* is confined to a bounded region (nothing past distance
`R` can beat `x_1`), and intersecting with a closed ball yields a compact set carrying the same infimum. The
hypothesis `y_0\notin X` is inessential for *existence* — if `y_0\in X` the nearest point is `y_0` itself with
`d=0`; its real role is only to make `d>0` (a positive distance) when one wants the nearest point distinct
from `y_0`. Closedness of `X` is essential: on an open or merely-non-closed set the infimum can fail to be
attained (e.g. `X=(0,1]\subset\mathbb R`, `y_0=0`, has `d=0` with no nearest point). The same "minimizing
sequence" idea proves it too: take `x_k\in X` with `\varphi(x_k)\to d`; the sequence is bounded (eventually
`\varphi(x_k)\le d+1`), so by Bolzano–Weierstrass a subsequence converges to some `x_0`, which lies in `X`
(closedness) and has `\varphi(x_0)=d` (continuity) — completeness of `\mathbb R^n` is what underlies both
routes.

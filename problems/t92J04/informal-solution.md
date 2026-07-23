<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t92J04: Every open cover of a compact metric space has a Lebesgue number

## Why It's Hard

The statement is about **uniformity**, and that is exactly the obstacle. Each point `x` lies in some cover
member `U`, and openness gives a ball `B(x, r_x)\subseteq U` — but the radius `r_x` can *shrink toward `0`*
as `x` moves (cover members may get thin), so there is no obvious single `\epsilon` that works everywhere.
The whole content is converting the *pointwise* "each `x` has room" into a *uniform* "one `\epsilon` works
for all small sets," and **compactness** is the only tool that bridges pointwise to uniform.

Two further subtleties:

- **From "small set" to "small ball."** A set `C` of diameter `<\epsilon` is not handed to you as a ball;
  but picking any `x\in C`, every point of `C` is within `\mathrm{diam}(C)<\epsilon` of `x`, so
  `C\subseteq B(x,\epsilon)`. This reduces the problem to trapping a *ball* around each point in some cover
  member.
- **Manufacturing a uniform radius.** The slick route encodes "how much room point `x` has" as a *positive
  continuous function*, namely the average distance to the complements of a finite subcover; compactness
  then makes its **minimum positive**, and that minimum is the Lebesgue number. The trick is seeing that the
  *maximum* term of the average forces a whole ball into one cover member.

## The Key Insight

Pass to a finite subcover `U_1,\dots,U_n` (compactness), and measure each point's "room" by
$$
f(x) = \frac1n\sum_{i=1}^n d\big(x,\ X\setminus U_i\big),
$$
the average distance from `x` to the complements. Then `f` is continuous and **strictly positive** (each `x`
is interior to some `U_i`, so that term is positive), so on the compact `X` it attains a **positive minimum**
`\epsilon := \min_X f > 0`. This `\epsilon` is a Lebesgue number: for a set `C` of diameter `<\epsilon`, take
`x\in C`, so `C\subseteq B(x,\epsilon)`; since `\max_i d(x, X\setminus U_i)\ge f(x)\ge\epsilon`, some `U_m`
has `d(x, X\setminus U_m)\ge\epsilon`, i.e. `B(x,\epsilon)\subseteq U_m`, whence `C\subseteq U_m`.

## Complete Proof

Let `(X, d)` be a compact metric space and `\mathcal U` an open cover. We produce `\epsilon>0` such that
every `C\subseteq X` with `\mathrm{diam}(C)<\epsilon` lies in some member of `\mathcal U`. (Recall
`\mathrm{diam}(C) = \sup_{a,b\in C} d(a,b)`, and `d(x, S) = \inf_{s\in S} d(x,s)` is the point-to-set
distance.)

**Step 1: a finite subcover.** Since `X` is compact, `\mathcal U` has a finite subcover
`U_1, U_2, \dots, U_n`. If some `U_i = X`, then *every* subset of `X` lies in `U_i` and any `\epsilon>0`
works; so assume each `U_i\ne X`, hence each complement `C_i := X\setminus U_i` is a nonempty closed set.

**Step 2: the "room" function.** Define `f : X\to\mathbb R` by
$$
f(x) = \frac1n\sum_{i=1}^n d(x, C_i), \qquad C_i = X\setminus U_i .
$$
Each `x\mapsto d(x, C_i)` is `1`-Lipschitz (hence continuous), so `f` is continuous.

**Step 3: `f` is strictly positive.** Fix `x\in X`. The subcover covers `X`, so `x\in U_i` for some `i`;
since `U_i` is open, there is `\delta>0` with `B(x,\delta)\subseteq U_i`, meaning every point within
`\delta` of `x` avoids `C_i = X\setminus U_i`. Hence `d(x, C_i)\ge\delta>0`, so
$$
f(x) \ge \frac1n\, d(x, C_i) > 0 .
$$
Thus `f(x)>0` for every `x\in X`.

**Step 4: a positive minimum.** `f` is a continuous, strictly positive function on the **compact** space
`X`, so by the extreme value theorem it attains a minimum:
$$
\epsilon := \min_{x\in X} f(x) > 0 .
$$

**Step 5: `\epsilon` is a Lebesgue number.** Let `C\subseteq X` with `\mathrm{diam}(C)<\epsilon`. If
`C=\varnothing`, it lies in any member trivially; otherwise pick a point `x\in C`. Every `c\in C` satisfies
`d(x,c)\le\mathrm{diam}(C)<\epsilon`, so
$$
C\subseteq B(x,\epsilon).
$$
Now since the average is at most the maximum term,
$$
\max_{1\le i\le n} d(x, C_i) \ge f(x) \ge \epsilon,
$$
so there is an index `m` with `d(x, C_m)\ge\epsilon`. This says exactly that the open ball `B(x,\epsilon)`
is disjoint from `C_m`: any `y\in C_m` has `d(x,y)\ge d(x,C_m)\ge\epsilon`, so `y\notin B(x,\epsilon)`.
Therefore
$$
B(x,\epsilon)\subseteq X\setminus C_m = U_m,
$$
and consequently
$$
C\subseteq B(x,\epsilon)\subseteq U_m\in\mathcal U .
$$

Since `C` was an arbitrary subset of diameter `<\epsilon`, this `\epsilon` is a **Lebesgue number** for
`\mathcal U`. ∎

**Remark.** Compactness is used twice, in its two equivalent metric guises, to manufacture uniformity:
once to reduce to *finitely many* cover members (so the average `f` is a finite, hence continuous, sum), and
once via the extreme value theorem to turn "`f>0` pointwise" into "`f\ge\epsilon>0` uniformly." A purely
sequential proof makes the same point: were there *no* Lebesgue number, then for each `n` some set `C_n` of
diameter `<1/n` would lie in no member; picking `x_n\in C_n`, a convergent subsequence `x_{n_k}\to x`
(sequential compactness) would land in some `U\ni x` with `B(x,r)\subseteq U`, and for large `k` both
`d(x_{n_k},x)<r/2` and `\mathrm{diam}(C_{n_k})<r/2` give `C_{n_k}\subseteq B(x,r)\subseteq U`, a
contradiction. Either way, the lemma fails without compactness — e.g. the cover
`\{(\,n,n+2\,) : n\in\mathbb Z\}\cup\dots` style covers of non-compact spaces admit sets of *every* positive
diameter escaping all members. The Lebesgue number is the metric incarnation of compactness's uniformizing
power, and it underlies, e.g., the proof that continuous maps on compacta are uniformly continuous.

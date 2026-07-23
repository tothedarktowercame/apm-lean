<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM t93A02: The Hausdorff metric on closed bounded sets is complete when the ground space is

## Why It's Hard

This is the completeness of the **Hausdorff metric** `(H, D)`, and the difficulty is that the limit is not a
point but a *whole set*, which must be built from below and then shown to be (i) nonempty, (ii) bounded,
(iii) closed, and (iv) the actual `D`-limit. Several traps:

- **Constructing the limit set.** A point of the limit should be approachable simultaneously from every
  `A_n`. The hint's device — limits of "threads" `(x_n)` with `x_n\in A_n` and `d(x_n,x_{n+1})<1/2^n` — is
  exactly engineered so each thread is *Cauchy* (`\sum 1/2^n<\infty`) and hence convergent **by completeness
  of `X`**. Completeness is used precisely here, to manufacture the limit points.
- **Threads run both ways.** To show `A_m` is close to `\bar A`, one must start a thread at an *arbitrary*
  `a\in A_m` and extend it *forward and backward* using the chaining `A_n\subseteq U(A_{n+1},1/2^n)` and
  `A_{n+1}\subseteq U(A_n,1/2^n)`. Forgetting the backward extension leaves `\bar A` possibly missing points
  near small-index `A_m`.
- **Closedness is genuinely delicate.** The strict consecutive bound `1/2^n` is too tight to "merge"
  threads, so a naive diagonal argument fails to show `\bar A` is closed. The clean fix: the Hausdorff
  distance **does not see closure** (`D(A,B)=D(A,\overline B)`), so one passes to `\overline{\bar A}`, which
  is automatically closed and bounded and is the same `D`-limit.

## The Key Insight

Pass to a fast subsequence with `D(A_n,A_{n+1})<1/2^n` (a Cauchy sequence converges once a subsequence does).
Then `D(A_n,A_{n+1})<1/2^n` means each point of `A_n` is within `1/2^n` of `A_{n+1}` and vice versa, so any
`a\in A_m` extends — forward and backward — to a **thread** `(x_n)`, `x_n\in A_n`, `d(x_n,x_{n+1})<1/2^n`,
which is Cauchy and (by completeness of `X`) converges into `\bar A`. The tail estimate
`d(x_m,\lim)\le\sum_{n\ge m}1/2^n = 1/2^{m-1}` gives, in both directions,
$$
A_m\subseteq U(\bar A, 1/2^{m-1}) \quad\text{and}\quad \bar A\subseteq U(A_m, 1/2^{m-1}) \implies D(A_m,\bar A)\le \tfrac{1}{2^{m-1}}\to 0.
$$
`\bar A` is bounded (it sits in `U(A_1,1)`); replacing it by its closure `\overline{\bar A}` (same `D`,
closure-invariant) gives a genuine element of `H`, the limit.

## Complete Proof

Throughout, `U(A,\epsilon)=\bigcup_{a\in A}B(a,\epsilon)` is the open `\epsilon`-neighborhood, and the
Hausdorff metric on nonempty closed bounded sets is
$$
D(A,B) = \inf\{\epsilon>0 : A\subseteq U(B,\epsilon)\ \text{and}\ B\subseteq U(A,\epsilon)\}.
$$
We use the standard consequence: if `D(A,B)<\epsilon` then `A\subseteq U(B,\epsilon)` and `B\subseteq
U(A,\epsilon)`; conversely those two inclusions give `D(A,B)\le\epsilon`. Assume `(X,d)` is complete and let
`\{A_n\}` be Cauchy in `(H,D)`.

### Step 0: reduce to a fast subsequence

Since a Cauchy sequence converges as soon as one of its subsequences does, choose indices `n_1<n_2<\cdots`
with `D(A_p,A_q)<1/2^k` for all `p,q\ge n_k`, and relabel so that (writing `A_n` for the subsequence)
$$
D(A_n, A_{n+1}) < \frac1{2^n}\qquad\text{for all } n. \tag{$\ast$}
$$
In particular `(\ast)` gives the **chaining inclusions**
$$
A_n\subseteq U\big(A_{n+1}, \tfrac1{2^n}\big) \quad\text{and}\quad A_{n+1}\subseteq U\big(A_n, \tfrac1{2^n}\big). \tag{chain}
$$

### Step 1: threads exist and converge

Call a sequence `(x_n)_{n\ge1}` a **thread** if `x_n\in A_n` for every `n` and `d(x_n,x_{n+1})<1/2^n` for
every `n`. Define
$$
\bar A = \{\, x\in X : x=\lim_n x_n \text{ for some thread } (x_n)\,\}.
$$

> **Extension Lemma.** For any `m` and any `a\in A_m`, there is a thread `(x_n)` with `x_m = a`.

*Proof.* Going forward (`n\ge m`): given `x_n\in A_n`, the first inclusion of (chain) puts `x_n\in
U(A_{n+1},1/2^n)`, so some `x_{n+1}\in A_{n+1}` has `d(x_n,x_{n+1})<1/2^n`. Going backward (`n<m`): given
`x_{n+1}\in A_{n+1}`, the second inclusion of (chain) puts `x_{n+1}\in U(A_n,1/2^n)`, so some `x_n\in A_n`
has `d(x_n,x_{n+1})<1/2^n`. Starting from `x_m=a` and extending both ways gives a thread. ∎

**Every thread converges.** For `q<p`, `d(x_q,x_p)\le\sum_{n=q}^{p-1}d(x_n,x_{n+1})<\sum_{n=q}^{\infty}
1/2^n = 1/2^{q-1}`, so `(x_n)` is Cauchy in the **complete** space `X` and converges to some `x\in X`, with
the **tail bound**
$$
d(x_m, x) = \lim_{p\to\infty} d(x_m, x_p) \le \sum_{n=m}^{\infty}\frac1{2^n} = \frac1{2^{m-1}}. \tag{tail}
$$
By definition `x\in\bar A`. In particular, extending any `a\in A_1` (nonempty) gives `\bar A\ne\varnothing`.

### Step 2: `D(A_m,\bar A)\le 1/2^{m-1}`

**(A) `A_m\subseteq U(\bar A, 1/2^{m-1})`.** Let `a\in A_m`. By the Extension Lemma take a thread with
`x_m=a`; its limit `x\in\bar A` satisfies, by (tail), `d(a,x)=d(x_m,x)\le 1/2^{m-1}`. So `a` is within
`1/2^{m-1}` of `\bar A`.

**(B) `\bar A\subseteq U(A_m, 1/2^{m-1})`.** Let `x\in\bar A` with witnessing thread `(x_n)`, `x_n\to x`.
Then `x_m\in A_m`, and by the same tail estimate (tail), `d(x,x_m)\le 1/2^{m-1}`. So `x` is within
`1/2^{m-1}` of `A_m`.

From (A) and (B), both defining inclusions of the Hausdorff metric hold with `\epsilon=1/2^{m-1}+\delta` for
every `\delta>0`, so
$$
D(A_m,\bar A) \le \frac1{2^{m-1}} \xrightarrow[m\to\infty]{} 0. \tag{conv}
$$

### Step 3: `\bar A` is bounded, and its closure is the limit in `H`

**Bounded.** By (B) with `m=1`, `\bar A\subseteq U(A_1, 1)`. As `A_1\in H` is bounded, say
`A_1\subseteq B(p,R)`, every `y\in U(A_1,1)` has `d(y,p)<R+1`, so `\bar A\subseteq B(p,R+1)` is **bounded**.

**Closing up.** Let `L := \overline{\bar A}`, the closure of `\bar A`. Then `L` is **closed**, **bounded**
(closure of the bounded set `\bar A`), and nonempty, so `L\in H`. Moreover the Hausdorff distance is
unchanged by closure: for any set `S`, `d(\cdot, S)=d(\cdot,\overline S)` and `d(\cdot,A_m)` is continuous,
so `\sup_{s\in\overline S}d(s,A_m)=\sup_{s\in S}d(s,A_m)`; hence `D(A_m, \bar A)=D(A_m, \overline{\bar A})=
D(A_m, L)`. Combining with (conv),
$$
D(A_m, L) = D(A_m, \bar A) \le \frac1{2^{m-1}} \to 0.
$$
So the (relabeled) subsequence converges to `L\in H`.

### Step 4: conclude

The chosen subsequence converges to `L\in H`; since the original sequence `\{A_n\}` is Cauchy and has a
convergent subsequence, it converges to the same limit `L`. Therefore every Cauchy sequence in `(H,D)`
converges in `H`, i.e. **`(H,D)` is complete.** ∎

**Remark.** Completeness of `X` is used at exactly one point — to make each Cauchy *thread* converge —
which is the engine producing the limit set `\bar A`. The summability `\sum 1/2^n<\infty` is what makes
threads Cauchy and supplies the geometric tail bound `1/2^{m-1}` controlling `D(A_m,\bar A)` in both
directions at once. The closure step is the clean way around a real subtlety: the strict consecutive bound
makes the raw thread-limit set `\bar A` awkward to prove closed, but the Hausdorff metric is blind to the
difference between a set and its closure, so `\overline{\bar A}` is the honest limit in `H`. This theorem —
that `H` inherits completeness — is the foundation for the contraction-mapping construction of fractals
(iterated function systems converge to their attractor in the complete space `(H,D)`).

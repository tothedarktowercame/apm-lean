<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96A02: Banach's contraction theorem, the iterate trick, and global Picard existence

## Why It's Hard

Banach's contraction theorem (a) is standard, but parts (b) and (c) are where the real idea lives, and it
is easy to under-appreciate. The naive application of the contraction theorem to the integral operator of
an ODE works only when the Lipschitz constant times the interval length is `< 1` — forcing you to shrink
the time interval and then patch local solutions together, which is awkward and does not immediately give
existence on the *whole* prescribed interval `[0,1]`.

The elegant resolution is part (b): even if `T` itself is not a contraction, it suffices that some
**iterate** `T^N` is. The subtlety is proving that a fixed point of `T^N` is automatically a fixed point of
`T` (and uniquely so) — a short but slippery argument that pushes `T` through the relation `T^N x^* = x^*`.
Then in (c) the payoff appears: the Picard operator on `[0,1]` may have Lipschitz constant `L \ge 1` (no
contraction), but its `N`-th iterate has constant `L^N/N!`, which tends to `0` because **the factorial
beats the exponential**. That single fact delivers global existence and uniqueness on all of `[0,1]`
without ever shrinking the interval.

## The Key Insight

- **(a)** Iterating a contraction makes a Cauchy sequence (`d(x_{n+1},x_n) \le k^n d(x_1,x_0)`, geometric),
  which converges in the complete space to the unique fixed point.
- **(b)** If `T^N` is a contraction with fixed point `x^*`, then `T x^*` is *also* a fixed point of `T^N`
  (since `T^N(Tx^*) = T(T^N x^*) = Tx^*`), and uniqueness of `T^N`'s fixed point forces `Tx^* = x^*`.
- **(c)** For `(Tu)(t) = u_0 + \int_0^t f(u(s))\,ds`, iterating the integral gives the sharp estimate

$$|T^n u(t) - T^n v(t)| \le \frac{L^n t^n}{n!}\,\|u - v\|_\infty \ \Longrightarrow\ \|T^N u - T^N v\|_\infty \le \frac{L^N}{N!}\,\|u-v\|_\infty,$$

  and since `L^N/N! \to 0`, some `T^N` is a contraction. By (b), `T` has a unique fixed point — the unique
  solution of the IVP on the full interval `[0,1]`, for *any* Lipschitz constant `L`.

## Complete Proof

### (a) Banach's contraction mapping theorem

**Theorem.** Let `(M,d)` be a complete metric space and `T : M \to M` a contraction: there is
`k \in [0,1)` with `d(Tx, Ty) \le k\,d(x,y)` for all `x,y`. Then `T` has a **unique** fixed point `x^*`,
and for every `x_0 \in M` the iterates `x_n = T^n x_0` converge to `x^*`.

**Proof.** Fix `x_0` and set `x_{n+1} = Tx_n`. By induction
`d(x_{n+1}, x_n) = d(Tx_n, Tx_{n-1}) \le k\,d(x_n, x_{n-1}) \le \dots \le k^n d(x_1, x_0)`. For `m > n`,
the triangle inequality and the geometric series give

$$d(x_m, x_n) \le \sum_{j=n}^{m-1} d(x_{j+1}, x_j) \le d(x_1,x_0)\sum_{j=n}^{m-1} k^j \le \frac{k^n}{1-k}\,d(x_1, x_0) \xrightarrow[n\to\infty]{} 0,$$

so `(x_n)` is Cauchy. By completeness `x_n \to x^*` for some `x^* \in M`. A contraction is continuous, so
`Tx^* = T(\lim x_n) = \lim Tx_n = \lim x_{n+1} = x^*`: `x^*` is a fixed point. **Uniqueness:** if
`Tx^* = x^*` and `Ty^* = y^*`, then `d(x^*, y^*) = d(Tx^*, Ty^*) \le k\,d(x^*, y^*)`, so
`(1-k)\,d(x^*,y^*) \le 0`, forcing `d(x^*, y^*) = 0`, i.e. `x^* = y^*`. ∎

### (b) If `T^N` is a contraction, `T` has a unique fixed point

Suppose `T^N` is a contraction for some `N \ge 1`. By part (a), `T^N` has a unique fixed point `x^*`.

**`x^*` is a fixed point of `T`.** Apply `T` to `T^N x^* = x^*` and use that powers of `T` commute:

$$T^N(Tx^*) = T(T^N x^*) = T x^*,$$

so `Tx^*` is also a fixed point of `T^N`. Since `T^N` has a *unique* fixed point, `Tx^* = x^*`.

**Uniqueness for `T`.** If `Ty = y`, then `T^N y = y`, so `y` is a fixed point of `T^N`, whence `y = x^*`.
Therefore `T` has the unique fixed point `x^*`. ∎

### (c) Global existence and uniqueness for `u' = f(u)`, `u(0) = u_0`

Let `f : \mathbb R \to \mathbb R` be Lipschitz: `|f(a) - f(b)| \le L|a-b|`. A function `u \in C[0,1]` solves
the IVP iff it solves the integral equation

$$u(t) = u_0 + \int_0^t f(u(s))\,ds =: (Tu)(t),$$

(differentiating recovers `u' = f(u)`, `u(0) = u_0`, and `u` is automatically `C^1`). Work in
`X = C[0,1]` with the sup norm — a complete metric space — and seek a fixed point of `T : X \to X`.

**Iterated Lipschitz estimate.** Claim: for all `n \ge 0` and `t \in [0,1]`,

$$|T^n u(t) - T^n v(t)| \le \frac{L^n t^n}{n!}\,\|u - v\|_\infty.$$

*Induction.* `n = 0` is `|u(t)-v(t)| \le \|u-v\|_\infty`. Assuming it for `n`,

$$|T^{n+1}u(t) - T^{n+1}v(t)| = \Big|\int_0^t \big[f(T^n u(s)) - f(T^n v(s))\big]ds\Big|
\le L\int_0^t |T^n u(s) - T^n v(s)|\,ds$$
$$\le L\int_0^t \frac{L^n s^n}{n!}\|u-v\|_\infty\,ds = \frac{L^{n+1} t^{n+1}}{(n+1)!}\,\|u-v\|_\infty.$$

Taking the supremum over `t \in [0,1]` (where `t^n \le 1`),

$$\|T^n u - T^n v\|_\infty \le \frac{L^n}{n!}\,\|u-v\|_\infty.$$

**Some iterate is a contraction.** Since `\dfrac{L^N}{N!} \to 0` as `N \to \infty` (the factorial dominates
the exponential), choose `N` with `\dfrac{L^N}{N!} < 1`. Then `T^N` is a contraction on the complete space
`X`.

**Conclusion.** By part (b), `T` has a unique fixed point `u \in C[0,1]`. This `u` satisfies the integral
equation, hence is `C^1` and solves

$$\boxed{\ u'(t) = f(u(t)) \ (0 < t < 1), \qquad u(0) = u_0,\ }$$

and it is the **unique** such solution. ∎

**Remark.** The whole force of part (b) is to remove the restriction "`L \cdot (\text{interval}) < 1`."
Iterating the Picard operator turns the dangerous factor `L^n` into `L^n/n!` because each composition
integrates one more time, manufacturing an extra `1/n!`. The factorial always wins, so existence and
uniqueness hold on the *entire* interval `[0,1]` for *any* Lipschitz constant — no shrinking, no patching.
This is the clean global form of the Picard–Lindelöf theorem.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95A01: The operator Newton–Schulz iteration converges to A⁻¹

## Why It's Hard

The iteration `B_{n+1} = 2B_n - B_n A B_n` is **Newton's method for the inverse** (the Schulz
iteration). The first task — showing the residuals `I - AB_n` and `I - B_n A` vanish — rests on one
slick algebraic identity, but it is easy to miss that the *right* and *left* residuals must be tracked
**separately** (operators don't commute), and that each obeys its own squaring recursion.

The deeper difficulty is part (c): "the residuals go to `0`" is **not** the same as "`B_n` converges
to an inverse." A priori the operators `B_n` could grow without bound even while `AB_n \to I` — this is
exactly what happens when `A` is close to non-invertible. To rule this out you need a **uniform bound**
`\|B_n\| \le K`, and that bound is not free: it requires the surjectivity of `A` (so that `B_n A \to I`
can be tested against *every* vector) together with the **uniform boundedness principle** to upgrade
pointwise boundedness to norm boundedness. Only then do the Newton increments become summable and `B_n`
converge. Seeing that UBP is the bridge from "residuals vanish" to "`B_n` is bounded" is the crux.

## The Key Insight

**The residuals square.** Let `R_n = I - AB_n` and `S_n = I - B_n A`. A one-line computation gives

$$R_{n+1} = (I - AB_n)^2 = R_n^2, \qquad S_{n+1} = (I - B_n A)^2 = S_n^2,$$

so `R_n = R_0^{\,2^n}` and `S_n = S_0^{\,2^n}`. Since `\|R_0\| = \|AB_0 - I\| < 1` and `\|S_0\| = \|B_0 A - I\| < 1`,
both residuals decay **quadratically** to `0`: `\|R_n\| \le \|R_0\|^{2^n} \to 0`. That is part (a).

For the rest, surjectivity of `A` makes every `y \in X` equal to `Az`, so `B_n y = (B_n A)z \to z` —
the sequence `(B_n y)` converges, hence is bounded, *for every* `y`. The **uniform boundedness
principle** then yields `\sup_n \|B_n\| =: K < \infty` (part b). With this bound the Newton increments
satisfy `\|B_{n+1} - B_n\| = \|B_n R_n\| \le K\|R_0\|^{2^n}`, which is summable, so `B_n` is Cauchy and
converges to a bounded `B`. Passing the limits `AB_n \to I`, `B_n A \to I` through gives `AB = BA = I`,
so `B = A^{-1}` (part c).

## Complete Proof

Throughout, `R_n := I - AB_n`, `S_n := I - B_n A`, and `r := \|R_0\| = \|AB_0 - I\| < 1`,
`s := \|S_0\| = \|B_0 A - I\| < 1`.

### (a) `AB_n \to I` and `B_n A \to I` in norm

Compute the right residual after one step, using `B_{n+1} = 2B_n - B_n A B_n`:

$$R_{n+1} = I - AB_{n+1} = I - 2AB_n + A B_n A B_n = I - 2AB_n + (AB_n)^2 = (I - AB_n)^2 = R_n^2.$$

By induction `R_n = R_0^{\,2^n}`, so, since `B(X)` is a Banach algebra,

$$\|I - AB_n\| = \|R_0^{\,2^n}\| \le \|R_0\|^{2^n} = r^{2^n} \xrightarrow[n\to\infty]{} 0,$$

because `r < 1`. Hence `AB_n \to I` in norm (quadratically). The identical computation on the left,

$$S_{n+1} = I - B_{n+1}A = I - 2B_n A + B_n A B_n A = (I - B_n A)^2 = S_n^2,$$

gives `S_n = S_0^{\,2^n}` and `\|I - B_n A\| \le s^{2^n} \to 0`, so `B_n A \to I` in norm. ∎

### (b) Uniform bound `\|B_n\| \le K` (using surjectivity and UBP)

Assume `A` is surjective: `\operatorname{ran} A = X`. Fix any `y \in X` and choose `z \in X` with
`y = Az`. Then by part (a),

$$B_n y = B_n (Az) = (B_n A) z \longrightarrow z, \qquad \text{since } \|(B_n A - I)z\| \le \|B_n A - I\|\,\|z\| \to 0.$$

A convergent sequence is bounded, so `\sup_n \|B_n y\| < \infty` for **every** `y \in X` (here
surjectivity is essential — it is what makes this hold for all `y`, not just `y \in \operatorname{ran} A`).
The `B_n` are bounded operators on the Banach space `X`, pointwise bounded, so by the **uniform
boundedness principle** (Banach–Steinhaus),

$$\boxed{\ K := \sup_n \|B_n\| < \infty,\qquad \|B_n\| \le K \ \text{ for all } n.\ }$$

### (c) `A` has a bounded inverse and `B_n \to A^{-1}`

**`B_n` converges.** The Newton increment is

$$B_{n+1} - B_n = 2B_n - B_n A B_n - B_n = B_n(I - AB_n) = B_n R_n,$$

so, by parts (a) and (b),

$$\|B_{n+1} - B_n\| \le \|B_n\|\,\|R_n\| \le K\, r^{2^n}.$$

Since `\sum_n K r^{2^n} < \infty` (the exponents `2^n` make it converge super-geometrically), the
telescoping series `B_n = B_0 + \sum_{k<n}(B_{k+1} - B_k)` is absolutely convergent. As `B(X)` is
complete, `B_n \to B` in operator norm for some `B \in B(X)`.

**`B` is a two-sided inverse of `A`.** Pass to the limit in part (a):

$$AB = \lim_n AB_n = I, \qquad BA = \lim_n B_n A = I$$

(both limits valid because `B_n \to B` in norm and multiplication is norm-continuous). Thus `A` is
invertible with bounded inverse

$$A^{-1} = B \in B(X).$$

**Convergence to `A^{-1}`.** Since `B_n \to B = A^{-1}` in operator norm, in particular

$$\boxed{\ B_n x \to A^{-1} x \quad \text{for every } x \in X.\ }$$

(Indeed the convergence is uniform on the unit ball: `\|B_n - A^{-1}\| = \|A^{-1}(AB_n - I)\| \le \|A^{-1}\|\, r^{2^n} \to 0`,
the same quadratic rate.) ∎

**Remark.** Parts (a) and (c) exhibit the hallmark of Newton's method — *quadratic* convergence, here
made precise by `R_n = R_0^{2^n}`. Part (b) is the load-bearing step: residual decay alone does not
control `\|B_n\|`, and without the surjectivity-plus-UBP bound the increments `B_n R_n` need not be
summable. The hypothesis `\operatorname{ran} A = X` and the uniform boundedness principle together are
exactly what convert quadratic residual decay into genuine convergence of the iterates to a bounded
inverse.

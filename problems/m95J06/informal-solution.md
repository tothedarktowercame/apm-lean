<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95J06: The ℓᵖ norm tends to ℓ^∞, and the Hilbert norm is smooth away from zero

## Why It's Hard

The two parts are independent, and each turns on spotting the *one* structural fact that trivializes it.

For (a), the `\ell^p` norm `(\sum |x_i|^p)^{1/p}` is an `n`-term sum, yet the claim is that as `p\to\infty`
it forgets all but the largest term. The difficulty is that *both* the base `\sum|x_i|^p` and the exponent
`1/p` move, so you cannot pass the limit inside naively. The clean route is a two-sided squeeze in which
the only surviving moving factor is `n^{1/p} \to 1` — the number of terms becomes irrelevant in the limit.

For (b), the norm `\|x\| = \sqrt{\langle x,x\rangle}` is built from a square root, and `\sqrt{\cdot}` is
*not* differentiable at `0`. So the norm has a genuine singularity at the origin (a cone point), and the
problem restricts to nonzero `x` for exactly that reason. The insight is that away from `0` the norm is a
composition of two differentiable maps — the smooth quadratic `x \mapsto \langle x,x\rangle` and the square
root, which is differentiable on `(0,\infty)`. The inner-product structure is essential: it makes
`\|x\|^2` a *polynomial*, which is why Hilbert norms are smooth off the origin while general Banach norms
need not be differentiable anywhere.

## The Key Insight

**(a)** Let `M = \|x\|_\infty = \max_i |x_i|`. Bounding the sum below by its largest term and above by `n`
copies of it,

$$M = (M^p)^{1/p} \le \Big(\sum_i |x_i|^p\Big)^{1/p} \le (n M^p)^{1/p} = n^{1/p} M,$$

so `M \le \|x\|_p \le n^{1/p}M`, and `n^{1/p} \to 1` squeezes `\|x\|_p \to M`.

**(b)** Write `N(x) = \|x\| = \sqrt{Q(x)}` with `Q(x) = \langle x,x\rangle`. `Q` is a quadratic with
derivative `DQ(x)h = 2\langle x,h\rangle`, and `\sqrt{\cdot}` is differentiable at `Q(x) = \|x\|^2 > 0`
when `x \ne 0`. By the chain rule `N` is differentiable with

$$DN(x)\,h = \frac{1}{2\sqrt{Q(x)}}\,DQ(x)h = \frac{\langle x,h\rangle}{\|x\|}, \qquad \nabla N(x) = \frac{x}{\|x\|}.$$

The gradient is the unit vector in the direction of `x`.

## Complete Proof

### (a) `\lim_{p\to\infty}\|x\|_p = \|x\|_\infty`

Fix `x \in \mathbb R^n` and let `M = \|x\|_\infty = \max_{1\le i\le n}|x_i|`. If `x = 0` both sides are `0`,
so assume `x \ne 0` (hence `M > 0`).

**Lower bound.** Some index `j` has `|x_j| = M`, and every term in the sum is nonnegative, so

$$\|x\|_p = \Big(\sum_{i=1}^n |x_i|^p\Big)^{1/p} \ge \big(|x_j|^p\big)^{1/p} = M.$$

**Upper bound.** Each `|x_i| \le M`, so `\sum_i |x_i|^p \le n\,M^p`, whence

$$\|x\|_p = \Big(\sum_{i=1}^n |x_i|^p\Big)^{1/p} \le (n M^p)^{1/p} = n^{1/p}\,M.$$

**Squeeze.** Combining, `M \le \|x\|_p \le n^{1/p} M` for all `p \ge 1`. Since `n` is fixed,
`n^{1/p} = e^{(\ln n)/p} \to e^0 = 1` as `p \to \infty`. Therefore both bounds converge to `M`, and

$$\boxed{\ \lim_{p\to\infty}\|x\|_p = M = \|x\|_\infty.\ }$$

### (b) The Hilbert-space norm is differentiable at every nonzero point

Let `H` be a real Hilbert space, `N(x) = \|x\| = \sqrt{\langle x,x\rangle}`, and fix `x \ne 0`.

**As a composition.** Write `N = g \circ Q`, where

$$Q(x) = \langle x,x\rangle \quad (H \to \mathbb R), \qquad g(s) = \sqrt{s} \quad ((0,\infty)\to\mathbb R).$$

`Q` is differentiable everywhere: by bilinearity and symmetry of the inner product,
`Q(x+h) - Q(x) = 2\langle x,h\rangle + \langle h,h\rangle`, where `h \mapsto 2\langle x,h\rangle` is a
bounded linear functional (Cauchy–Schwarz: `|2\langle x,h\rangle| \le 2\|x\|\|h\|`) and the remainder
`\langle h,h\rangle = \|h\|^2 = o(\|h\|)`. Hence `DQ(x)h = 2\langle x,h\rangle`. Since `x \ne 0`,
`Q(x) = \|x\|^2 > 0`, and `g(s) = \sqrt s` is differentiable there with `g'(Q(x)) = \tfrac{1}{2\|x\|}`.

**Chain rule.** Therefore `N = g \circ Q` is (Fréchet) differentiable at `x`, with

$$\boxed{\ DN(x)\,h = g'(Q(x))\,DQ(x)h = \frac{1}{2\|x\|}\cdot 2\langle x,h\rangle = \frac{\langle x,h\rangle}{\|x\|},\ }$$

i.e. `\nabla N(x) = x/\|x\|`.

**Direct confirmation of the remainder estimate.** Writing `a = \|x\|^2 > 0` and
`b = 2\langle x,h\rangle + \|h\|^2`, rationalizing gives `N(x+h) - N(x) = \sqrt{a+b} - \sqrt a = \dfrac{b}{\sqrt{a+b}+\sqrt a}`,
and one checks

$$N(x+h) - N(x) - \frac{\langle x,h\rangle}{\|x\|}
= \Big[\sqrt{a+b}-\sqrt a - \frac{b}{2\sqrt a}\Big] + \frac{\|h\|^2}{2\sqrt a}.$$

For `\|h\|` small enough that `|b| \le a/2`, the bracket is `O(b^2/a^{3/2}) = O(\|h\|^2)` (the second-order
Taylor bound for `\sqrt{\cdot}`), and the last term is `O(\|h\|^2)`; hence the whole remainder is
`O(\|h\|^2) = o(\|h\|)`. This confirms `DN(x)h = \langle x,h\rangle/\|x\|`. ∎

**Remark.** The restriction to `x \ne 0` is essential: at `x = 0` the norm is *not* differentiable —
`\sqrt{\cdot}` has a vertical tangent at `0`, and the norm has a cone singularity (e.g. on `\mathbb R`,
`\|x\| = |x|` has the familiar corner). What rescues differentiability elsewhere is purely the
inner-product structure: `\|x\|^2 = \langle x,x\rangle` is a smooth quadratic, so the only obstruction is
the square root at the origin. General Banach-space norms lack this `\sqrt{\text{polynomial}}` form and can
fail to be differentiable at *every* point (e.g. `\|\cdot\|_1` or `\|\cdot\|_\infty` on `\mathbb R^n`),
which is also why part (a)'s limiting norm `\|\cdot\|_\infty` is non-smooth.

<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m96A05: Central-difference discretization of a two-point BVP, and nonsingularity of the resulting system

## Why It's Hard

Part (a) is mostly bookkeeping — substitute the two difference quotients into the ODE and collect
terms — but it is easy to drop the factor of `h^2`, mis-sign the first-derivative weight `±(h/2)a_i`,
or forget that the Dirichlet data `u(0)=0`, `u(1)=1` are **not unknowns**: they must be moved to the
right-hand side, which shrinks the system from `n+2` nominal nodes to an `n×n` system in the interior
values and modifies the first and last equations.

Part (b) is where the real content lives. "Nonsingular" is a statement about *every* right-hand side at
once, so you cannot just exhibit a solution — you must rule out a nontrivial null vector. The natural
tool is **strict diagonal dominance**, but two things can break it, and the hypotheses are tuned exactly
to repair them:

- The off-diagonal entries `1 ± (h/2)a_i` have *no fixed sign* — `a(t)` may be positive or negative and
  large. If `(h/2)|a_i| > 1` one off-diagonal flips sign and the row's off-diagonal absolute-value sum
  becomes `h|a_i|`, which can **exceed** the diagonal. This is exactly why "`h` sufficiently small" is
  needed: it forces both neighbors to stay nonnegative so the sum collapses to the clean value `2`.
- With `b ≡ 0` the diagonal is exactly `−2` and the interior off-diagonal sum is exactly `2`: dominance
  is only *weak*, and weak dominance alone does **not** guarantee nonsingularity. The hypothesis
  `b(t) < 0` supplies a strictly positive margin `h^2|b_i|` on every diagonal entry, upgrading weak to
  **strict** dominance — and strict dominance is what forbids a null vector.

So the two hypotheses are not decoration: small `h` controls the convection term `a`, and `b<0` controls
the zeroth-order term `b`, and you need both.

## The Key Insight

Write the discrete equation at interior node `t_i = ih` and multiply through by `h^2`. The scheme is a
**tridiagonal** system whose `i`-th row has entries

$$
\underbrace{\Big(1-\tfrac{h}{2}a_i\Big)}_{\text{left }\ell_i}\;u_{i-1}
\;+\;\underbrace{\big(-2+h^2 b_i\big)}_{\text{diag }d_i}\;u_i
\;+\;\underbrace{\Big(1+\tfrac{h}{2}a_i\Big)}_{\text{right }r_i}\;u_{i+1}\;=\;h^2 c_i .
$$

Now compare diagonal against off-diagonals. Since `a` is continuous on `[0,1]` it is bounded,
`|a(t)| ≤ M_a`; choose `h < 2/M_a`, so `(h/2)|a_i| < 1` and **both** off-diagonals are positive:

$$|\ell_i|+|r_i| = \Big(1-\tfrac{h}{2}a_i\Big)+\Big(1+\tfrac{h}{2}a_i\Big) = 2 .$$

Meanwhile `b_i < 0` gives `d_i = -2 + h^2 b_i < -2`, so

$$|d_i| = 2 - h^2 b_i = 2 + h^2|b_i| \;>\; 2 \;=\; |\ell_i|+|r_i| .$$

Every row is **strictly** diagonally dominant, with a uniform margin `h^2|b_i| > 0`. A strictly
diagonally dominant matrix is nonsingular (Levy–Desplanques / Gershgorin) — equivalently, a max-modulus
argument on any putative null vector hits a contradiction. That is the whole proof.

## Complete Proof

### (a) Derivation of the discrete system

Place a uniform mesh `t_i = ih`, `i = 0,1,…,n+1`, `h = 1/(n+1)`, and let `u_i` denote the approximation
to `u(t_i)`. Abbreviate `a_i = a(t_i)`, `b_i = b(t_i)`, `c_i = c(t_i)`. At each **interior** node
`i = 1,…,n`, replace the derivatives in `u''(t)+a(t)u'(t)+b(t)u(t)=c(t)` by the given central
differences:

$$
\frac{u_{i+1}-2u_i+u_{i-1}}{h^2}
\;+\; a_i\,\frac{u_{i+1}-u_{i-1}}{2h}
\;+\; b_i\,u_i \;=\; c_i .
$$

Multiply by `h^2` and group by `u_{i-1}, u_i, u_{i+1}`:

$$
\Big(1-\tfrac{h}{2}a_i\Big)u_{i-1}
\;+\;\big(-2+h^2 b_i\big)u_i
\;+\;\Big(1+\tfrac{h}{2}a_i\Big)u_{i+1}
\;=\; h^2 c_i,
\qquad i = 1,\dots,n. \tag{$\ast$}
$$

The boundary conditions are imposed exactly: `u_0 = 0` and `u_{n+1} = 1`. These two values are **known**,
so they are removed from the list of unknowns and carried to the right-hand side wherever they appear:

- In equation `i = 1`, the term `(1-\tfrac{h}{2}a_1)u_0` vanishes because `u_0 = 0`; the right-hand side
  stays `h^2 c_1`.
- In equation `i = n`, the term `(1+\tfrac{h}{2}a_n)u_{n+1}` becomes the known quantity
  `1+\tfrac{h}{2}a_n` (since `u_{n+1}=1`) and is subtracted from the right-hand side, giving
  `h^2 c_n - \big(1+\tfrac{h}{2}a_n\big)`.

What remains is an `n×n` **tridiagonal** linear system `T\mathbf{u} = \mathbf{f}` in the interior
unknowns `\mathbf{u} = (u_1,\dots,u_n)^{\mathsf T}`, where the `i`-th row of `T` carries

$$
\ell_i = 1-\tfrac{h}{2}a_i \ (\text{sub-diagonal}), \quad
d_i = -2+h^2 b_i \ (\text{diagonal}), \quad
r_i = 1+\tfrac{h}{2}a_i \ (\text{super-diagonal}),
$$

with `\ell_1` and `r_n` absent (folded into `\mathbf{f}`), and

$$
\mathbf{f} = \big(h^2 c_1,\; h^2 c_2,\; \dots,\; h^2 c_{n-1},\; h^2 c_n - (1+\tfrac{h}{2}a_n)\big)^{\mathsf T}.
$$

Solving this banded system (e.g. by the tridiagonal Thomas algorithm) and appending `u_0=0`,
`u_{n+1}=1` yields the approximate solution `\{u_i\}_{i=0}^{n+1}` to the boundary value problem. ∎

### (b) The system `T` is nonsingular for `b<0` and `h` small

**Choice of `h`.** Since `a` is continuous on the compact interval `[0,1]`, it is bounded:
`M_a := \max_{t\in[0,1]}|a(t)| < \infty`. Require `h` small enough that

$$
\frac{h}{2}\,M_a < 1, \qquad\text{i.e.}\qquad h < \frac{2}{M_a}
$$

(if `a ≡ 0`, no constraint from this; any `h>0` works). Then for every interior index `i`,
`(h/2)|a_i| < 1`, so both off-diagonal entries are **positive**:

$$
\ell_i = 1-\tfrac{h}{2}a_i > 0, \qquad r_i = 1+\tfrac{h}{2}a_i > 0 .
$$

**Off-diagonal absolute-value sum.** Because both are positive, in any row that has both neighbors,

$$
|\ell_i| + |r_i| = \Big(1-\tfrac{h}{2}a_i\Big) + \Big(1+\tfrac{h}{2}a_i\Big) = 2 ,
$$

and in the two boundary rows (where one neighbor was folded into `\mathbf f`) the off-diagonal sum is
strictly smaller: `|r_1| < 2` and `|\ell_n| < 2`. Hence **every** row of `T` has off-diagonal
absolute-value sum `\le 2`.

**Strict diagonal dominance from `b<0`.** Since `b_i < 0`, we have `h^2 b_i < 0`, so
`d_i = -2 + h^2 b_i < -2 < 0` and therefore

$$
|d_i| = 2 - h^2 b_i = 2 + h^2|b_i| \;>\; 2 \;\ge\; \big(\text{off-diagonal sum of row } i\big).
$$

Thus `T` is **strictly diagonally dominant by rows**, with strict inequality in every row and a uniform
positive margin `h^2|b_i| > 0`.

**Nonsingularity (max-modulus / Gershgorin argument).** Suppose, for contradiction, that
`T\mathbf{u} = \mathbf{0}` for some `\mathbf{u} \ne \mathbf{0}`. Pick an index `k` attaining the maximum
modulus, `|u_k| = \max_i |u_i| > 0`. The `k`-th equation reads
`d_k u_k + \ell_k u_{k-1} + r_k u_{k+1} = 0` (omit any out-of-range neighbor), so

$$
|d_k|\,|u_k| = \big|\,\ell_k u_{k-1} + r_k u_{k+1}\,\big|
\le \big(|\ell_k| + |r_k|\big)\,\max_i|u_i|
\le 2\,|u_k|.
$$

Dividing by `|u_k| > 0` gives `|d_k| \le 2`. But strict dominance says `|d_k| = 2 + h^2|b_k| > 2` — a
contradiction. Hence the only solution of `T\mathbf{u}=\mathbf 0` is `\mathbf u = \mathbf 0`, so `T` is
**nonsingular** and the discrete boundary value problem has a unique solution for every right-hand side
`\mathbf f`. ∎

**Remark (why both hypotheses are sharp).** If `b ≡ 0` the diagonal equals `−2` and interior rows have
`|d_i| = 2 = |\ell_i|+|r_i|`: dominance degenerates to weak, the max-modulus contradiction collapses, and
singular configurations can occur — so `b<0` is what makes the margin strict. If instead `h` is large
enough that `(h/2)|a_i| > 1`, one off-diagonal flips sign, the off-diagonal sum jumps to `h|a_i|`, and
for `h|a_i| > 2 + h^2|b_i|` dominance fails — so "`h` sufficiently small" is exactly the condition that
keeps the convection term from overwhelming diffusion. Both hypotheses are load-bearing.

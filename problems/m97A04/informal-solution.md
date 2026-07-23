<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m97A04: Finite-difference solution of a two-point BVP and uniqueness of the discrete system for b < 0, small h

## Why It's Hard

The first half is a derivation: substitute the central-difference quotients into `u'' + au' + bu = c` at
the interior mesh points and read off the linear system. The pitfalls are clerical but unforgiving — drop
the `h²` factor, mis-sign the convection weight `±(h/2)a_i`, or forget that the homogeneous data
`u(0)=u(1)=0` *remove* the endpoints from the unknowns — and the system is wrong.

The real content is the uniqueness proof. "The linear equations have a unique solution" is the statement
that the `n×n` coefficient matrix `T` is **nonsingular**, i.e. its only null vector is `0`. You cannot
exhibit a solution to prove this; you must forbid a nontrivial homogeneous solution. The natural tool is
**strict diagonal dominance**, and the two hypotheses are exactly what make it work — each repairing a
distinct failure mode:

- The off-diagonal entries `1 ± (h/2)a_i` have **no fixed sign** (`a` may be large of either sign). If
  `(h/2)|a_i| > 1`, one of them flips sign and the row's off-diagonal absolute-value sum jumps from the
  clean value `2` to `h|a_i|`, which can swamp the diagonal. *This is why `h` must be small*: it keeps the
  convection term from overpowering diffusion.
- With `b ≡ 0` the interior diagonal is exactly `−2` and the off-diagonal sum is exactly `2`: dominance is
  only **weak**, which does not by itself guarantee nonsingularity. The hypothesis `b(t) < 0` gives every
  diagonal a strictly positive margin `h²|b_i|`, upgrading weak to **strict** dominance — and strict
  dominance is what kills the null vector.

So small `h` controls `a`, and `b<0` controls `b`; both are load-bearing.

## The Key Insight

Discretize on the uniform mesh `t_i = ih`, `h = 1/(n+1)`, multiply the difference equation through by
`h²`, and collect terms. The scheme is a **tridiagonal** system whose `i`-th interior row is

$$
\underbrace{\Big(1-\tfrac h2 a_i\Big)}_{\ell_i}\,u_{i-1}
+ \underbrace{\big(-2 + h^2 b_i\big)}_{d_i}\,u_i
+ \underbrace{\Big(1+\tfrac h2 a_i\Big)}_{r_i}\,u_{i+1}
= h^2 c_i,
$$

with `u_0 = u_{n+1} = 0`. Compare diagonal against off-diagonals. Since `a` is continuous on `[0,1]` it is
bounded, `|a| ≤ M_a`; take `h < 2/M_a`, so `(h/2)|a_i| < 1` and both off-diagonals are positive, giving
the off-diagonal absolute-value sum

$$|\ell_i| + |r_i| = \Big(1-\tfrac h2 a_i\Big) + \Big(1+\tfrac h2 a_i\Big) = 2,$$

while `b_i < 0` forces

$$|d_i| = 2 - h^2 b_i = 2 + h^2|b_i| \;>\; 2.$$

Every row is **strictly** diagonally dominant, so a max-modulus argument shows the homogeneous system has
only the zero solution: `T` is nonsingular and the discrete BVP has a unique solution.

## Complete Proof

### Step 1: derivation of the discrete system

Lay a uniform mesh `t_i = ih`, `i = 0,1,…,n+1`, with `h = 1/(n+1)`, so `t_0 = 0` and `t_{n+1} = 1`. Let
`u_i` approximate `u(t_i)`, and write `a_i = a(t_i)`, `b_i = b(t_i)`, `c_i = c(t_i)`. At each **interior**
node `i = 1,…,n` replace the derivatives in `u'' + au' + bu = c` by the given quotients (the second
formula is the central difference for `u'`):

$$
\frac{u_{i+1} - 2u_i + u_{i-1}}{h^2} + a_i\,\frac{u_{i+1} - u_{i-1}}{2h} + b_i u_i = c_i .
$$

Multiply by `h²` and group by `u_{i-1}, u_i, u_{i+1}`:

$$
\boxed{\ \Big(1 - \tfrac h2 a_i\Big)\,u_{i-1} + \big(-2 + h^2 b_i\big)\,u_i + \Big(1 + \tfrac h2 a_i\Big)\,u_{i+1} = h^2 c_i,\qquad i = 1,\dots,n.\ }
$$

The boundary conditions `u(0)=u(1)=0` are imposed exactly as `u_0 = 0` and `u_{n+1} = 0`. In the equation
`i=1` the term `(1-\tfrac h2 a_1)u_0` vanishes; in `i=n` the term `(1+\tfrac h2 a_n)u_{n+1}` vanishes.
Hence both endpoints drop out and the unknowns are the interior values `\mathbf u = (u_1,\dots,u_n)^{\mathsf T}`.
The result is the `n × n` **tridiagonal** linear system

$$
T\,\mathbf u = h^2\,\mathbf c, \qquad \mathbf c = (c_1,\dots,c_n)^{\mathsf T},
$$

where row `i` of `T` carries sub-diagonal `\ell_i = 1 - \tfrac h2 a_i`, diagonal `d_i = -2 + h^2 b_i`, and
super-diagonal `r_i = 1 + \tfrac h2 a_i` (with `\ell_1` and `r_n` absent). Explicitly,

$$
T =
\begin{pmatrix}
d_1 & r_1 & & & \\
\ell_2 & d_2 & r_2 & & \\
& \ddots & \ddots & \ddots & \\
& & \ell_{n-1} & d_{n-1} & r_{n-1} \\
& & & \ell_n & d_n
\end{pmatrix}.
$$

Solving this banded system (e.g. by the tridiagonal Thomas algorithm) and appending `u_0 = u_{n+1} = 0`
gives the numerical solution `\{u_i\}_{i=0}^{n+1}`.

### Step 2: for `b < 0` and small `h`, `T` is nonsingular (unique solution)

**Choice of `h`.** Since `a` is continuous on the compact interval `[0,1]`, it is bounded:
`M_a := \max_{t\in[0,1]}|a(t)| < \infty`. Require `h` small enough that

$$
\frac h2 M_a < 1 \qquad\Longleftrightarrow\qquad h < \frac{2}{M_a}
$$

(if `a ≡ 0`, any `h>0` works). Then `(h/2)|a_i| < 1` for every interior `i`, so both off-diagonal entries
are **positive**:

$$
\ell_i = 1 - \tfrac h2 a_i > 0, \qquad r_i = 1 + \tfrac h2 a_i > 0 .
$$

**Off-diagonal sums.** Because both are positive, each interior row (having both neighbors) satisfies

$$
|\ell_i| + |r_i| = \Big(1 - \tfrac h2 a_i\Big) + \Big(1 + \tfrac h2 a_i\Big) = 2,
$$

and the two end rows (one neighbor folded into the boundary) have strictly smaller off-diagonal sum
`|r_1| < 2`, `|\ell_n| < 2`. Hence **every** row has off-diagonal absolute-value sum `≤ 2`.

**Strict diagonal dominance from `b < 0`.** Since `b_i < 0`, `h^2 b_i < 0`, so `d_i = -2 + h^2 b_i < -2`
and

$$
|d_i| = 2 - h^2 b_i = 2 + h^2 |b_i| \;>\; 2 \;\ge\; \big(\text{off-diagonal sum of row } i\big).
$$

Thus `T` is **strictly diagonally dominant by rows**, with a uniform positive margin `h^2|b_i| > 0` in
every row.

**Nonsingularity (max-modulus argument).** Suppose `T\mathbf u = \mathbf 0` for some
`\mathbf u \ne \mathbf 0`. Choose an index `k` with `|u_k| = \max_i |u_i| > 0`. Row `k` reads
`d_k u_k + \ell_k u_{k-1} + r_k u_{k+1} = 0` (omit any out-of-range neighbor), so

$$
|d_k|\,|u_k| = \big|\,\ell_k u_{k-1} + r_k u_{k+1}\,\big|
\le \big(|\ell_k| + |r_k|\big)\,\max_i |u_i|
\le 2\,|u_k| .
$$

Dividing by `|u_k| > 0` gives `|d_k| \le 2`, contradicting `|d_k| = 2 + h^2|b_k| > 2`. Hence the only
solution of `T\mathbf u = \mathbf 0` is `\mathbf u = \mathbf 0`, so `T` is nonsingular. Therefore, for
every right-hand side, the system `T\mathbf u = h^2\mathbf c` has a **unique** solution. ∎

**Remark (sharpness of the hypotheses).** If `b ≡ 0` the interior diagonal is exactly `−2` and the
off-diagonal sum is exactly `2`: dominance is only weak, the strict inequality `|d_k| > 2` is lost, and
the max-modulus contradiction collapses — so `b < 0` is precisely what supplies the strict margin. If
instead `h` is so large that `(h/2)|a_i| > 1`, an off-diagonal flips sign, the off-diagonal sum becomes
`h|a_i|`, and for `h|a_i| > 2 + h^2|b_i|` dominance fails — so "small `h`" is precisely what keeps
convection from overwhelming diffusion. Both hypotheses are essential.

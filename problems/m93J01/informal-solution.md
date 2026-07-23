<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m93J01: Numerov's method — a compact sixth-order scheme for the Schrödinger operator

## Why It's Hard

The naive way to discretize `Ly = -y'' + Vy` is to replace `y''_n` by the centered
second difference `(y_{n+1} - 2y_n + y_{n-1})/h^2`. That is only second order: the
leading error is a term `\propto h^4 y^{(\mathrm{iv})}_n`, computed in part (a). To
do better you would normally widen the stencil (use `y_{n\pm 2}`), which wrecks the
clean tridiagonal structure and complicates boundary handling.

The whole problem is a guided discovery of the trick that avoids this — **Numerov's
method** — and the difficulty is conceptual, not computational. You must see that the
offending `h^4 y^{(\mathrm{iv})}` term need not be discarded *or* attacked with more
grid points: because `y` solves the differential equation, `y^{(\mathrm{iv})}` can be
*re-expressed through the equation itself* (`y'' = Vy \Rightarrow y^{(\mathrm{iv})} = (Vy)''`)
and then approximated by a second difference (part (c)) that folds back onto the same
three points `n-1, n, n+1`. The payoff is a still-tridiagonal, three-term recurrence
whose truncation error jumps from `O(h^4)` to `O(h^6)`. The hard part is trusting that
"use the ODE to lower the order of the error term" is legitimate and seeing exactly
where to insert it.

> Two transcription slips in the problem are corrected below: the remainders written
> `o(h^6)`/`o(h^4)` are really `O(h^6)`/`O(h^4)` (the next omitted term is of that
> exact order), and the part-(b) identity needs an `h^2` factor on `(Ly)_n` and a `+`
> in front of `\kappa h^4 y^{(\mathrm{iv})}` to be true. Everything else is as stated.

## The Key Insight

Two Taylor expansions and one substitution do all the work.

1. **Centered second difference (part a).** The odd derivatives cancel, leaving
   `y_{n+1} + y_{n-1} - 2y_n = h^2 y''_n + \tfrac{1}{12} h^4 y^{(\mathrm{iv})}_n + O(h^6)`,
   so `\kappa = 1/12`. This same identity, applied to the function `y''`, is part (c).

2. **Eliminate the `h^4` term using the equation.** For a solution of `Ly = 0` we have
   `y'' = Vy`, hence `y^{(\mathrm{iv})} = (Vy)''`. Part (c) lets us replace
   `h^2 y^{(\mathrm{iv})}_n` by the second difference of `Vy` — a quantity living on the
   same three nodes. Substituting this into the `\kappa h^4 y^{(\mathrm{iv})}` error term
   *cancels it to order* `h^6` while only modifying the coefficients of `y_{n\pm1}` and
   `y_n` by `V`-dependent factors. The stencil never grows.

The result is Numerov's recurrence, a compact sixth-order scheme.

## Complete Proof

Throughout, `y_n = y(nh)`, `v_n = V(nh)`, and `y` is assumed smooth enough for the
Taylor expansions (`C^6` for parts (a), (b); `C^6` of `y''`, i.e. `C^8`, for the
sharp remainder in (c)). The basic centered Taylor expansion is

$$y_{n\pm1} = y_n \pm h y'_n + \tfrac{h^2}{2} y''_n \pm \tfrac{h^3}{6} y'''_n
+ \tfrac{h^4}{24} y^{(\mathrm{iv})}_n \pm \tfrac{h^5}{120} y^{(\mathrm v)}_n
+ \tfrac{h^6}{720} y^{(\mathrm{vi})}_n + \cdots .$$

---

### (a)  The value of `\kappa`

Adding the `n+1` and `n-1` expansions, all odd-order terms cancel:

$$y_{n+1} + y_{n-1} = 2y_n + h^2 y''_n + \tfrac{h^4}{12} y^{(\mathrm{iv})}_n
+ \tfrac{h^6}{360} y^{(\mathrm{vi})}_n + \cdots,$$

since `2\cdot\tfrac{1}{24} = \tfrac{1}{12}` and `2\cdot\tfrac{1}{720} = \tfrac{1}{360}`.
Therefore

$$\boxed{\,y_{n+1} + y_{n-1} - 2y_n = h^2 y''_n + \tfrac{1}{12} h^4 y^{(\mathrm{iv})}_n
+ O(h^6),\qquad \kappa = \tfrac{1}{12}.\,}$$

The omitted remainder is `\tfrac{1}{360} h^6 y^{(\mathrm{vi})}_n + O(h^8) = O(h^6)`. ∎

---

### (b)  The discrete Schrödinger operator

At node `n`, `(Ly)_n = -y''_n + v_n y_n`, so `h^2(Ly)_n = -h^2 y''_n + h^2 v_n y_n`.
From part (a), `-h^2 y''_n = -(y_{n+1} + y_{n-1} - 2y_n) + \kappa h^4 y^{(\mathrm{iv})}_n + O(h^6)`.
Hence

$$h^2 (Ly)_n = -(y_{n+1} + y_{n-1} - 2y_n) + h^2 v_n y_n + \kappa h^4 y^{(\mathrm{iv})}_n + O(h^6),$$

i.e.

$$\boxed{\,h^2 (Ly)_n = -y_{n+1} - y_{n-1} + (2 + h^2 v_n)\,y_n
+ \kappa h^4 y^{(\mathrm{iv})}_n + O(h^6).\,}$$

This is the intended identity (with the `h^2` factor restored and `+\kappa h^4`). The
combination `-y_{n+1} - y_{n-1} + (2 + h^2 v_n)y_n` is the second-order discrete
Schrödinger operator; its discrepancy from `h^2(Ly)_n` is exactly the
`-\kappa h^4 y^{(\mathrm{iv})}` term we will cancel in (d). ∎

---

### (c)  Second difference of `y''`

Apply the identity of part (a) to the function `w = y''` in place of `y` (its second
derivative is `w'' = y^{(\mathrm{iv})}`):

$$y''_{n+1} + y''_{n-1} - 2y''_n = h^2 y^{(\mathrm{iv})}_n
+ \tfrac{1}{12} h^4 y^{(\mathrm{vi})}_n + O(h^6).$$

Since `\tfrac{1}{12} h^4 y^{(\mathrm{vi})}_n + O(h^6) = O(h^4)`,

$$\boxed{\,y''_{n+1} + y''_{n-1} - 2y''_n = h^2 y^{(\mathrm{iv})}_n + O(h^4).\,}$$

Only the leading order is needed here, so `\kappa` plays no role. ∎

---

### (d)  A sixth-order scheme for `Ly = 0`

We seek a difference equation whose residual on the exact solution is `O(h^6)`. Start
from part (b) with `(Ly)_n = 0`:

$$0 = -y_{n+1} - y_{n-1} + (2 + h^2 v_n)\,y_n + \kappa h^4 y^{(\mathrm{iv})}_n + O(h^6). \tag{$\ast$}$$

The only term we cannot evaluate from nodal values of `y` is `\kappa h^4 y^{(\mathrm{iv})}_n`.
**Use the equation to remove it.** For a solution of `Ly = 0`, `y'' = Vy`, so at every
node `y''_m = v_m y_m`, and `y^{(\mathrm{iv})} = (y'')'' = (Vy)''`. Part (c), applied to
`y''` and then using `y''_m = v_m y_m`, gives

$$h^2 y^{(\mathrm{iv})}_n = \big(y''_{n+1} + y''_{n-1} - 2y''_n\big) + O(h^4)
= \big(v_{n+1} y_{n+1} + v_{n-1} y_{n-1} - 2 v_n y_n\big) + O(h^4).$$

Multiply by `\kappa h^2`:

$$\kappa h^4 y^{(\mathrm{iv})}_n
= \kappa h^2\big(v_{n+1} y_{n+1} + v_{n-1} y_{n-1} - 2 v_n y_n\big) + O(h^6).$$

Substituting into `(\ast)` (the `O(h^4)` is multiplied by `\kappa h^2`, becoming
`O(h^6)`):

$$0 = -y_{n+1} - y_{n-1} + (2 + h^2 v_n) y_n
+ \tfrac{h^2}{12}\big(v_{n+1} y_{n+1} + v_{n-1} y_{n-1} - 2 v_n y_n\big) + O(h^6),$$

using `\kappa = 1/12`. Collecting the coefficients of `y_{n+1}, y_n, y_{n-1}`:

- `y_{n+1}`: `-1 + \tfrac{h^2}{12} v_{n+1} = -\big(1 - \tfrac{h^2}{12} v_{n+1}\big)`,
- `y_{n-1}`: `-1 + \tfrac{h^2}{12} v_{n-1} = -\big(1 - \tfrac{h^2}{12} v_{n-1}\big)`,
- `y_n`: `(2 + h^2 v_n) - \tfrac{2h^2}{12} v_n = 2 + \tfrac{5h^2}{6} v_n`.

Dropping the `O(h^6)` residual gives **Numerov's scheme**:

$$\boxed{\;\Big(1 - \tfrac{h^2}{12} v_{n+1}\Big) y_{n+1}
- \Big(2 + \tfrac{5h^2}{6} v_n\Big) y_n
+ \Big(1 - \tfrac{h^2}{12} v_{n-1}\Big) y_{n-1} = 0.\;}$$

**Order.** When the exact solution of `Ly = 0` is substituted, the left-hand side
equals the residual `O(h^6)` we discarded; the local truncation error is `O(h^6)`, so
the scheme has order `6`, as required. It is a three-term (tridiagonal) recurrence: the
stencil is no wider than the naive second-order method, yet four orders of accuracy are
gained — the entire benefit of expressing `y^{(\mathrm{iv})}` through the differential
equation rather than through extra grid points.

Given two starting values `y_0, y_1` (from initial/boundary data), the recurrence
propagates the solution:

$$y_{n+1} = \frac{\big(2 + \tfrac{5h^2}{6} v_n\big) y_n
- \big(1 - \tfrac{h^2}{12} v_{n-1}\big) y_{n-1}}{\,1 - \tfrac{h^2}{12} v_{n+1}\,}. \qquad\blacksquare$$

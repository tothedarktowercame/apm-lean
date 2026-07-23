<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM m95J03: Left inverses, the discontinuity of Jordan form, and exponentials of a nilpotent block

## Why It's Hard

These five parts look unrelated but are tied together by **Jordan structure and nilpotency**, and each
probes a place where naive intuition fails. Part (a) is a logic trap: an algebraic manipulation that
proves *uniqueness* is mistaken for a proof of *existence*. Part (b) confronts the surprising fact that
the Jordan canonical form — a discrete invariant — is **not** a continuous function of the matrix:
eigenvalues can collide under perturbation and fuse separate blocks into one, so the block structure
jumps. Parts (c)–(e) then exploit the opposite phenomenon: when a matrix is nilpotent, its exponential
series **terminates**, turning an infinite analytic object into a finite polynomial computation.

The subtle through-line is the matrix `B(0)`, which is a *single `4\times4` nilpotent Jordan block* — the
maximally degenerate limit of the diagonalizable family `B(\rho)`. That one fact explains the
discontinuity in (b), makes the exponential in (d) a four-term series, and turns the ODE in (e) into a
chain of integrators with a polynomial solution.

## The Key Insight

- **(a)** From `Ax = b` and `LA = I` one gets `x = Lb` — but this is valid only *assuming a solution
  already exists*. It shows the solution, *if any*, must be `Lb` (uniqueness), not that `Lb` solves the
  system. Solvability requires `b \in \operatorname{col}(A)`; otherwise `A(Lb) = (AL)b \ne b` because
  `AL \ne I` in general.
- **(b)** `B(\rho)` is lower-triangular with eigenvalues `\rho, \rho^2, \rho^3, \rho^4`. For generic
  `\rho` these are distinct, so `B(\rho)` is *diagonalizable* (JCF `= \operatorname{diag}`). At `\rho = 0`
  they all coalesce to `0` and `B(0)` is a *single nilpotent block*. The JCF jumps — **not continuous**.
- **(c)** `e^A = \sum A^k/k! = P e^J P^{-1}`, and on each Jordan block `J = \lambda I + N`,
  `e^J = e^\lambda \sum_{j<s} N^j/j!` (finite, since `N^s = 0`).
- **(d)/(e)** For the nilpotent `N = B(0)`, `e^{tN} = I + tN + \tfrac{t^2}{2}N^2 + \tfrac{t^3}{6}N^3`, and
  `x(t) = e^{tN}v` is the polynomial solution of the integrator chain `x_1' = 0, x_2' = x_1, \dots`.

## Complete Proof

### (a) Critique of the left-inverse "method"

A left inverse `L` (`LA = I_n`) exists iff `A` has full column rank (so `A` is injective, requiring
`n \le m`). The hint's chain is logically:

$$Ax = b \ \Longrightarrow\ LAx = Lb \ \Longrightarrow\ x = Lb.$$

Every step is correct, but note the chain **starts by assuming `x` is a solution**. So all it proves is:
*if* a solution exists, it must equal `Lb` — i.e. the solution is **unique**. It does **not** prove that
`Lb` *is* a solution. To check that, substitute:

$$A(Lb) = (AL)\,b,$$

and `AL` is an `m\times m` matrix that is generally **not** `I_m` (it equals `I_m` only if `A` also has a
right inverse, i.e. is invertible). Indeed `Ax = b` has a solution iff `b \in \operatorname{col}(A)`:

- If `b \in \operatorname{col}(A)`, then a solution `x_0` exists, and the chain gives `x_0 = Lb`, so `Lb`
  *is* the (unique) solution.
- If `b \notin \operatorname{col}(A)`, there is **no** solution, yet the "method" still outputs the vector
  `Lb`, which satisfies `A(Lb) \ne b`. The method silently produces a non-solution.

So the statement is flawed: it conflates **necessary** with **sufficient** and assumes consistency. (Two
further caveats: when `m > n` the left inverse `L` is **not unique**, and for inconsistent `b` different
choices of `L` give different `Lb` — none of them solutions; and if `A` lacks full column rank, no left
inverse exists at all, so the method cannot even begin.) The honest statement: a left inverse certifies
*uniqueness* and recovers the solution *when the system is consistent* (`b \in \operatorname{col}(A)`).

### (b) Jordan form is not continuous

`B(\rho)` is lower triangular, so its eigenvalues are the diagonal entries `\rho, \rho^2, \rho^3, \rho^4`.

- **For generic `\rho`** (e.g. `0 < |\rho| < 1`, where `\rho,\rho^2,\rho^3,\rho^4` are four *distinct*
  numbers), `B(\rho)` has four distinct eigenvalues, hence is **diagonalizable**:
  `\mathrm{JCF}(B(\rho)) = \operatorname{diag}(\rho,\rho^2,\rho^3,\rho^4)` — four `1\times1` blocks.
- **At `\rho = 0`,** all eigenvalues coalesce to `0` and

$$B(0) = \begin{pmatrix} 0&0&0&0 \\ 1&0&0&0 \\ 0&1&0&0 \\ 0&0&1&0 \end{pmatrix},$$

  the nilpotent down-shift. Its eigenvalue `0` has *geometric* multiplicity `1` (rank `B(0) = 3`, so
  `\dim\ker = 1`), so `B(0)` is a **single `4\times4` Jordan block** `J_4(0)`.

As `\rho \to 0`, `B(\rho) \to B(0)` continuously (entrywise), but
`\mathrm{JCF}(B(\rho)) = \operatorname{diag}(\rho,\rho^2,\rho^3,\rho^4) \to \operatorname{diag}(0,0,0,0) = 0`,
whereas `\mathrm{JCF}(B(0)) = J_4(0) \ne 0`. The limit of the Jordan forms is **not** the Jordan form of
the limit. Hence **the Jordan canonical form is not a continuous function of the matrix.** (The block
structure is encoded in the integers `\operatorname{rank}(B-\lambda I)^k`, which jump as eigenvalues
collide; the diagonalizing similarities `P(\rho)` blow up as `\rho \to 0`.)

### (c) The matrix exponential via Jordan form

For any square `A`, define

$$e^A = \sum_{k=0}^\infty \frac{A^k}{k!},$$

which converges absolutely (`\|A^k/k!\| \le \|A\|^k/k!`, summable). Writing `A = PJP^{-1}` with `J` the
Jordan form, `A^k = P J^k P^{-1}`, so `e^A = P e^J P^{-1}`, and `e^J` is block-diagonal over the Jordan
blocks. For one block `J = \lambda I + N` of size `s` (`N` the nilpotent superdiagonal, `N^s = 0`), since
`\lambda I` and `N` commute,

$$e^{J} = e^{\lambda I}e^{N} = e^\lambda \sum_{j=0}^{s-1} \frac{N^j}{j!}, \qquad
\big(e^{J}\big)_{i,i+j} = \frac{e^\lambda}{j!}\ (0 \le j \le s-1),$$

an upper-triangular block with `e^\lambda` on the diagonal and `e^\lambda/j!` on the `j`-th superdiagonal.
Thus `e^A = P\,\operatorname{diag}(e^{J_1}, \dots, e^{J_r})\,P^{-1}`.

### (d) Compute `e^{B(0)}`

`B(0) = N` is nilpotent with `N^4 = 0`, so the series terminates:
`e^{N} = I + N + \tfrac{1}{2}N^2 + \tfrac16 N^3`. The powers of the down-shift are:
`N` has `1`'s on the first subdiagonal, `N^2` on the second, `N^3` in the `(4,1)` corner. Hence

$$\boxed{\ e^{B(0)} = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 1 & 1 & 0 & 0 \\ \tfrac12 & 1 & 1 & 0 \\ \tfrac16 & \tfrac12 & 1 & 1 \end{pmatrix}.\ }$$

(Lower triangular, `1`'s on the diagonal, and `1, \tfrac12, \tfrac16` on the successive subdiagonals.)

### (e) Solve `\mathbf x' = B(0)\mathbf x`, `\mathbf x(0) = \mathbf v`

The solution is `\mathbf x(t) = e^{tB(0)}\mathbf v`. Since `(tN)^k = t^k N^k` and `N^4 = 0`,

$$e^{tN} = I + tN + \frac{t^2}{2}N^2 + \frac{t^3}{6}N^3
= \begin{pmatrix} 1 & 0 & 0 & 0 \\ t & 1 & 0 & 0 \\ \tfrac{t^2}{2} & t & 1 & 0 \\ \tfrac{t^3}{6} & \tfrac{t^2}{2} & t & 1 \end{pmatrix}.$$

Therefore, with `\mathbf v = (v_1, v_2, v_3, v_4)^T`,

$$\boxed{\ \mathbf x(t) = \begin{pmatrix} v_1 \\[2pt] v_1 t + v_2 \\[2pt] v_1 \tfrac{t^2}{2} + v_2 t + v_3 \\[2pt] v_1 \tfrac{t^3}{6} + v_2 \tfrac{t^2}{2} + v_3 t + v_4 \end{pmatrix}.\ }$$

This matches solving the system directly: `B(0)` shifts coordinates down, so the equations are
`x_1' = 0`, `x_2' = x_1`, `x_3' = x_2`, `x_4' = x_3` — a **chain of integrators**, solved successively to
give the polynomials above (degree rising with depth, capped at `3` by the nilpotency `N^4 = 0`). ∎

**Remark.** Nilpotency is the unifying mechanism: `B(0) = J_4(0)` is the single nilpotent block that the
diagonalizable family `B(\rho)` degenerates into (the source of the JCF discontinuity in (b)), and that
same nilpotency truncates the exponential series to four terms (d) and forces the ODE solution to be a
cubic polynomial in `t` (e). Part (a) is the reminder that, even in pure linear algebra, "the algebra
produced a formula" is not the same as "the formula solves the problem."

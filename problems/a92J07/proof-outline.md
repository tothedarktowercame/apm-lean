# Proof Outline: a92J07

## Problem

u,v : ℝ² → ℝ C¹ with u_x = v_y, u_y = -v_x (Cauchy-Riemann).
If v(x,y) = 0 implies u(x,y) > 0, prove u,v are constant.

## Proof

f = u + iv is entire (from CR). f(ℂ) ⊆ slitPlane (from hypothesis).
g = log ∘ f is entire (Differentiable.clog), |Im g| ≤ π (arg bounds).
h = e^{ig} is bounded entire → constant by Liouville → g constant → f constant.

## Proven infrastructure (zero-sorry up to Liouville)

1. `Differentiable.clog` composition: log∘f is entire
2. `|Im(log f)| ≤ π`: argument bound via neg_pi_lt_arg + arg_le_pi
3. h = exp(I·log f) is bounded: ‖h(z)‖ ≤ e^π via norm_exp + Im bound
4. Liouville application: exists_const_forall_eq_of_bounded

## Remaining sorries (2)

1. `entire_avoids_ray_const` (line 74): From "h = exp(I·log f) constant" to "f constant".
   Requires: deriv(log f) = 0 via chain rule + exp_ne_zero, then zero-derivative → constant.
2. `cauchy_riemann_ray_implies_const` (line 88): CR-to-complex reduction.

## Lean state

- **Checked:** exit 0, 0 errors, 2 sorries
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a92J07/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- Key Mathlib: `Differentiable.clog`, `exists_const_forall_eq_of_bounded`,
  `neg_pi_lt_arg`, `arg_le_pi`, `norm_exp`

# Proof Outline: a94A04

## Problem

f in L^2([0,1]) with integral x^n f(x) dx = 0 for all n >= 0 implies f = 0 a.e.

## Proof

By linearity, integral p(x) f(x) dx = 0 for all polynomials p.
By Stone-Weierstrass, polynomials dense in C([0,1]), hence in L^2.
So f orthogonal to dense subspace → ||f||^2 = 0 → f = 0 a.e.

## Proven zero-sorry (partial structure)

- `orthogonal_to_polynomials`: Polynomial induction framework set up via
  `Polynomial.induction_on'` with monomial and add cases.
- Main theorem statement with correct Mathlib types.

## Remaining sorries (3)

1. Monomial case: connecting a*x^n integral to horth n
2. Add case: integral_add for interval integrals on Measure ℝ
3. Main theorem: Stone-Weierstrass + Lp density + Cauchy-Schwarz

## Lean state

- **Checked:** exit 0, 0 errors, 3 sorries
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a94A04/lean/Main.lean`

## References

- Key Mathlib: `boundedContinuousFunction_dense`, `subalgebra_topologicalClosure_eq_top_of_separatesPoints`,
  `Polynomial.induction_on'`, `MemLp`, `eval_monomial`, `eval_add`

# Proof Outline: m93A02

The Lean artifact proves the nonsurjective counterexample, constructs the
bounded algebraic inverse, closes the degenerate `M = 0` case, and proves the
quadratic Lipschitz estimate. One positive-`M` fixed-point assembly remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93A02.md`

## Formalized

- The lower bound makes `L` injective; with surjectivity this gives a
  `LinearEquiv H K`.
- Its inverse satisfies `‖L⁻¹ k‖ ≤ δ⁻¹ ‖k‖`.
- If `M = 0`, the bilinear term vanishes identically and `h = L⁻¹k` proves the
  quantitative local-solvability conclusion directly.
- The estimate
  `‖Q x x - Q y y‖ ≤ M * (‖x‖ + ‖y‖) * ‖x-y‖` is formalized.
- `apm_m93a02_contraction_constants` proves both numerical inequalities needed
  for invariance of the radius-`2‖k‖/δ` ball and contraction factor `< 1/2`.
- The explicit parabola counterexample proves failure without surjectivity.

## Remaining Boundary

For `M > 0`, define `h ↦ L⁻¹(k - Q h h)` on the closed ball of radius
`2‖k‖/δ`, prove self-mapping and contraction for `‖k‖ < δ²/(8M)`, and apply
`ContractingWith.exists_fixedPoint'`. The `M = 0` case and the required
quadratic difference bound are complete. All scalar parameter arithmetic is
also complete; only the restricted-map packaging and fixed-point extraction
remain.

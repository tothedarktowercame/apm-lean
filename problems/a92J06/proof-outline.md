# Proof Outline: a92J06

## Problem

Evaluate ∫₀²π 1/(2 + cos θ) dθ via contour integration. **Answer: 2π/√3.**

## Proof

Substitute z = e^{iθ}: dθ = dz/(iz), cos θ = (z + z⁻¹)/2.
The integral becomes ∮_{|z|=1} 2/(i(z² + 4z + 1)) dz.
Factor z² + 4z + 1 = (z - z₁)(z - z₂) with z₁ = -2+√3, z₂ = -2-√3.
Only z₁ is inside |z| < 1. By residue theorem: result = 2π/√3.

## Proven lemmas (zero-sorry)

1. `sqrt_three_gt_one`: √3 > 1
2. `sq_sqrt_three_complex`: (√3 : ℂ)² = 3
3. `quadratic_factor`: z²+4z+1 = (z-z₁)(z-z₂) via `linear_combination`
4. `z1_norm_lt_one`: |z₁| = 2-√3 < 1
5. `z2_norm_gt_one`: |z₂| = 2+√3 > 1

## Remaining sorries (2 sorries)

1. `contour_integral_eval`: Partial fractions + `integral_sub_inv_of_mem_ball`
2. `integral_inv_two_plus_cos`: z = e^{iθ} substitution

## Lean state

- **Checked:** exit 0, 0 errors, 2 sorries
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a92J06/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- Key Mathlib: `integral_sub_inv_of_mem_ball`, `circleIntegral`

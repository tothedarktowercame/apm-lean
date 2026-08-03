# Proof Outline: a96A05

## Problem

Prove that for any polynomial P ∈ ℂ[z], sup_{|z|=1} |1/z - P(z)| ≥ 1.

## Answer: The bound holds — 1/z cannot be uniformly approximated by polynomials.

## Proof

Use the contour integral. The integral of 1/z around the unit circle is 2πi
(winding number 1), while the integral of any polynomial is 0 (Cauchy's theorem).
So ∮ (1/z - P(z)) dz = 2πi, and |2πi| = 2π.

The ML inequality bounds |∮ f dz| ≤ 2π · sup|f| on the unit circle.
Combining: 2π ≤ 2π · sup, hence sup ≥ 1.

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Complete (0 sorries, 0 errors)
- **Key Mathlib lemmas**:
  - `circleIntegral.integral_sub_inv_of_mem_ball`: ∮ (z-w)⁻¹ = 2πI for w ∈ ball c R
  - `circleIntegral.norm_integral_le_of_norm_le_const`: ML inequality
  - `DiffContOnCl.circleIntegral_eq_zero`: Cauchy's theorem for entire functions
  - `circleIntegral.integral_sub`: linearity of contour integral
  - `ciSup_subtype`: relating ciSup over a set to ciSup over the subtype
  - `le_ciSup`: ciSup is an upper bound (with BddAbove)
- **Commit**: (see git log)

## References

- informal-solution: `../futon3c/data/apm-informal-proofs/apm-a96A05.md`
- problem TeX: `../apm/a96A05.tex`

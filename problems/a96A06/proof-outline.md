# Proof Outline: a96A06

## Problem

f is analytic except at a simple pole at z = 1, with ∮_{|z|=2} f(z)dz = -2πi.
Show f^(n)(0)/n! → 1.

## Proof strategy

1. Residue computation: from ∮f = -2πi and the residue theorem, Res(f,1) = -1.
2. Decomposition: f(z) = 1/(1-z) + g(z) where g is entire (removable singularity at z=1).
3. Taylor coefficients of 1/(1-z) at 0 are all 1 (geometric series).
4. Taylor coefficients of entire g → 0 (Cauchy estimates: |g^(n)(0)/n!| ≤ M(R)/R^n → 0 for R > 1).
5. f^(n)(0)/n! = 1 + g^(n)(0)/n! → 1.

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Partial (1 sorry; frozen main statement is false)
- **Proven lemmas**:
  - `cauchy_estimate_taylor`: Cauchy estimate |g^(n)(0)/n!| ≤ C/R^n for entire g
  - `geom_iteratedDeriv`: the nth derivative of `(1-z)⁻¹` at zero is `n!`
  - `geom_taylor_coeff`: every Taylor coefficient of `(1-z)⁻¹` is one
  - `entire_coeffs_tendsto_zero`: Taylor coefficients of entire function → 0 (via Cauchy estimates + squeeze)
- **Remaining sorry**:
  - `taylor_coeffs_tend_to_one`: false as stated.  The function
    `f(z) = (1-z)⁻¹ + (z-1)⁻²` has the required contour integral, but its
    normalized Taylor coefficients are `n+2`, not a sequence tending to one.
- **Required repair**: assume the singularity at `1` is at most a simple pole
  (or otherwise rule out every higher-order/essential principal part).

## References

- informal-solution: `../futon3c/data/apm-informal-proofs/apm-a96A06.md`
- problem TeX: `../apm/a96A06.tex`

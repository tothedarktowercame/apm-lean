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
- **Status**: Partial (2 sorries)
- **Proven lemmas**:
  - `cauchy_estimate_taylor`: Cauchy estimate |g^(n)(0)/n!| ≤ C/R^n for entire g
  - `entire_coeffs_tendsto_zero`: Taylor coefficients of entire function → 0 (via Cauchy estimates + squeeze)
- **Remaining sorries**:
  - `geom_iteratedDeriv`: iteratedDeriv n (1-z)⁻¹ 0 = n! (needs function-level induction with chain rule)
  - `taylor_coeffs_tend_to_one`: main theorem (needs residue theorem + removable singularity)
- **Blockers**: The residue theorem for computing Res(f,1) = -1 from the contour integral, and the removable singularity theorem for showing g = f - 1/(1-z) is entire, are the Mathlib theory boundary.

## References

- informal-solution: `../futon3c/data/apm-informal-proofs/apm-a96A06.md`
- problem TeX: `../apm/a96A06.tex`

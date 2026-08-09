# Proof Outline: a96J08

## Problem

Evaluate ∫_{-∞}^{∞} e^{ωx}/(1-e^x) dx for complex ω with 0 < Re(ω) < 1.
Answer: -π cot(πω).

## Proof strategy

Rectangular contour with corners -R and R+2πi. Period shift on top edge:
f(x+2πi) = e^{2πiω} f(x). Vertical edges vanish (0 < Re(ω) < 1). Poles at z=0
and z=2πi contribute half-residues via indentation. Functional equation:
I(1 - e^{2πiω}) = -πi(1 + e^{2πiω}), giving I = -π cot(πω).

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Partial (1 sorry)
- **Closer hop 2 progress**: proved the pointwise reflection identity
  `integrand (1 - ω) (-x) = -integrand ω x`.  This is the algebraic core of
  the corresponding principal-value symmetry and reduces an eventual
  evaluation to half of the critical strip.
- **Blocker**: The residue theorem for rectangular contours (boundary integral =
  2πi × sum of interior residues) is not available in Mathlib. Mathlib has
  `integral_boundary_rect_eq_zero_of_differentiableOn` (Cauchy-Goursat for
  rectangles, zero-residue case) but not the general residue version. The proof
  requires either excising a small disk around the interior pole at z=2πi and
  applying Cauchy-Goursat to the punctured region, or proving the convergence
  of shifted-edge integrals as the shift parameter ε → 0.  A further search
  for principal-value substitutions, beta/reflection integrals, cotangent
  integrals, and rectangle residue results found no packaged theorem that
  supplies the missing normalization.
- **Exact handoff theorem**: `apm_a96J08_bridge_1` now states the missing
  principal-value evaluation directly using the same interval integrals and
  `𝓝[>] 0` filter as the frozen theorem. Proving it leaves no substitution or
  normalization step unresolved.
- **Mid-solve lookups**: psr_search "residue theorem rectangle boundary integral
  pole differentiable countable Cauchy-Goursat" — timed out, no relevant patterns.
  memory_search ["contour", "integral", "residue"] — empty.

## References

- informal-solution: `informal-solution.md`
- problem TeX: `problem.tex`

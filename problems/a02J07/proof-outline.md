# Proof Outline: a02J07

## Problem

Let γ : [0,1] → ℂ be piecewise smooth with γ(0) = π and
γ⁻¹([0,∞)) = {0}. Prove that 0 < |Im ∫_γ dz/z| < 2π.

## Formalisation Approach

### Statement repair

The informal proof proposes an `arg_star` function with range (0, 2π),
branched along [0,∞). Mathlib's `Complex.arg` has range (-π, π] and
`Complex.log` is defined on `slitPlane = {z : 0 < z.re ∨ z.im ≠ 0}`
(the complement of (-∞,0]). Our domain Ω = ℂ \ [0,∞) is the mirror image.

**Structural repair:** The map z ↦ -z sends Ω biholomorphically onto
slitPlane. We define `logStar z = log(-z) + iπ`, giving a genuine branch of
log on Ω with imaginary part `argStar z ∈ (0, 2π)`. All properties derive
from Mathlib's existing `Complex.log` API — no invariant is bypassed.

### Proven infrastructure (zero-sorry lemmas)

1. **`posSlitPlane`**: domain Ω = {z : z.re < 0 ∨ z.im ≠ 0}
2. **`mem_posSlitPlane_iff`**: z ∈ Ω ↔ ¬(z.im = 0 ∧ 0 ≤ z.re)
3. **`neg_mem_slitPlane_of_posSlitPlane`**: negation maps Ω → slitPlane
4. **`posSlitPlane_ne_zero`**: z ∈ Ω ⟹ z ≠ 0
5. **`argStar_eq`**: argStar z = Complex.arg(-z) + π
6. **`hasDerivAt_logStar`**: d/dz[logStar z] = z⁻¹ on Ω (antiderivative of 1/z)
7. **`argStar_pos`**: z ∈ Ω ⟹ 0 < argStar z
8. **`argStar_lt_two_pi`**: z ∈ Ω ⟹ argStar z < 2π

### Remaining sorry boundary (2 sorries)

1. **`logIntegral_im_eq_argStar_diff`**: Expresses Im ∫_γ dz/z as
   argStar(γ(1)) - lim_{t→0+} argStar(γ(t)). Requires the fundamental theorem
   of calculus for interval integrals with a one-sided limit at t=0, where
   logStar is not defined (γ(0) = π is on the slit [0,∞)).

2. **`logIntegral_im_bounds`** (main theorem): Combines the FTC result with
   a case split on whether γ initially enters the upper or lower half-plane
   (determining lim_{t→0+} argStar(γ(t)) = 0 or 2π), then applies the strict
   bounds argStar(γ(1)) ∈ (0, 2π) to conclude 0 < |Im ∫| < 2π.

## Lean state

- **Checked:** exit 0, 0 errors, 2 sorries
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a02J07/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a02J07.md`

# Proof Outline: a96A07

## Problem

g is analytic in a neighborhood of the closed unit disk and one-to-one on the unit circle.
Show g maps Δ one-to-one onto the bounded domain D whose boundary is C = g(Γ).

## Proof strategy (informal)

1. g(Γ) = C is a Jordan curve (injective continuous image of a circle).
2. By the argument principle: for w ∉ C, the number of preimages of w under g in Δ
   equals the winding number of C around w.
3. Since C is a simple closed curve, winding number is 1 for interior, 0 for exterior.
4. Each interior point has exactly one preimage → g is injective and surjective onto D.

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Partial (1 sorry)
- **Reusable progress**:
  - `ConstructionTargets.Rouche` supplies a divisor-based argument principle
    and zero-count transfer on disks.
  - `ConstructionTargets.UnivalentDeriv.deriv_ne_zero_of_injOn` proves the
    nonvanishing derivative conclusion once interior injectivity is known.
  - `apm_a96A07_isConnected_image_disk` proves the canonical disk image is
    connected.
  - `apm_a96A07_isBounded_image_disk` proves it is bounded via the compact
    closed-disk image.
  - `apm_a96A07_isOpen_image_disk` proves it is open directly from the complex
    open-mapping theorem; boundary injectivity excludes the constant branch.
- **Remaining blockers**:
  - **Jordan curve theorem**: injective continuous image of circle bounds a domain — not formalized
  - **Winding number = 1 for simple closed curves** — not formalized
  - Identification of the bounded complementary component with the image and
    proof of the exact frontier equality.

## Closer Hop 3

Openness no longer depends on Jordan separation. The analytic function is
holomorphic on a slightly larger open ball, so Mathlib's open-mapping theorem
applies; its constant alternative contradicts injectivity of the two boundary
points `1` and `-1`. The final unresolved content is precisely the deep
topological implication from an embedded boundary circle to winding number
one, which is needed for interior injectivity and the exact frontier identity.

## References

- informal-solution: `../futon3c/data/apm-informal-proofs/apm-a96A07.md`
- problem TeX: `../apm/a96A07.tex`

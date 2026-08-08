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
- **Remaining blockers**:
  - **Jordan curve theorem**: injective continuous image of circle bounds a domain — not formalized
  - **Winding number = 1 for simple closed curves** — not formalized
  - Identification of the bounded complementary component with the image and
    proof of the exact frontier equality.

## References

- informal-solution: `../futon3c/data/apm-informal-proofs/apm-a96A07.md`
- problem TeX: `../apm/a96A07.tex`

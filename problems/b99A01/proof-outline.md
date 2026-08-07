# Proof Outline: b99A01

The Lean proof is complete.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b99A01.md`

## Formal route

1. Rotate the upper half-plane to the right half-plane and apply
   `PhragmenLindelof.right_half_plane_of_bounded_on_real`.
2. Turn the range-based fraction axiom into a `ValuationRing V` instance.
   Ideal totality, uniqueness of the maximal ideal, and the Bézout property
   then follow from Mathlib instances.
3. Package the displayed equation as the monic polynomial
   `X^n + ∑ i, C (a i) X^i - C b`; valuation rings are integrally closed, so
   its root comes from `V`.
4. Model an intermediate subring `W` as
   `ValuationSubring.ofSubring W`. Its local-ring instance supplies the unique
   maximal ideal. Prove the displayed fraction equality directly by splitting
   on whether `x` or `x⁻¹` comes from `V`, and by identifying elements outside
   the maximal ideal with units.

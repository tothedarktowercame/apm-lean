# Proof Outline: a96J02

## Problem

Let A and B be Lebesgue measurable subsets of ℝ with positive measure. Prove
A+B = {a+b | a∈A, b∈B} contains a nonempty open interval (Steinhaus's theorem).

## Strategy: Convolution of indicator functions

1. **Reduce to finite measure**: Intersect A, B with bounded intervals to get
   A', B' with 0 < μ(A'), μ(B') < ∞. ✓ PROVEN.

2. **Define overlap function**: f(x) = μ(A' ∩ (x - B')) =
   ∫ 1_{A'}(t) · 1_{B'}(x-t) dt.

3. **Positive integral**: ∫f dx = μ(A')μ(B') > 0 by Fubini.

4. **Continuity**: f is continuous (L¹ translation continuity). ✗ BOUNDARY.

5. **Conclusion**: ∫f > 0 ⟹ f(x₀) > 0 somewhere ⟹ by continuity f > 0 on
   open neighborhood ⟹ A'+B' ⊃ open interval ⊂ A+B. ✓ (framework ready).

## Proven components

- `exists_pos_measure_bounded_subset`: positive-measure set contains bounded
  positive-measure subset.
- `integrable_indicator_of_finite_measure`: indicator of finite-measure
  measurable set is integrable.
- `A' + B' ⊆ A + B`: set addition containment for intersections.

## Boundary (1 sorry)

The L¹ translation continuity for indicator functions: the map
x ↦ ∫ 1_{A'}(t) · 1_{B'}(x-t) dt is continuous. Standard in real analysis
but requires either the density of C_c in L¹ or the Lebesgue density theorem,
neither available in this Mathlib version in the needed form.

## Key Mathlib API used

- `measure_iUnion_le`, `Real.volume_Icc`, `measure_mono`
- `integrable_indicator_iff`, `aestronglyMeasurable_const`
- `Set.Pointwise` for set addition notation

## Dependencies

- `e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density`
  (convolution continuity via compact support density)
- `math-informal/monotone-approximation` (measure-theoretic approximation)

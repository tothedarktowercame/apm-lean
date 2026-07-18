# Proof Outline: a93J01

## Problem

f : [0,1] → ℝ continuous, BV, and AC on [a,1] for all 0 < a < 1.
Prove f is AC on [0,1].

## Proof

BV gives V(f, [0,a]) → 0 as a → 0⁺. Choose a₀ with V(f, [0,a₀]) < ε/2.
AC on [a₀,1] gives δ. Split disjoint intervals: those near 0 contribute
≤ V(f, [0, 2a₀]) < ε/2; those in [a₀,1] contribute < ε/2 by AC. Total < ε.

## Key Mathlib tools

- `BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left`: V(f,[0,a]) → 0
- `AbsolutelyContinuousOnInterval`: AC definition
- `absolutelyContinuousOnInterval_iff`: ε-δ characterization
- `eVariationOn.mono`: monotonicity of variation

## Remaining sorry (1)

`ac_on_01_of_continuous_bv_ac_from_a`: The main theorem. Requires
combinatorial bookkeeping of interval partition + connecting eVariationOn
to the AC ε-δ definition.

## Lean state

- **Checked:** exit 0, 0 errors, 1 sorry
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a93J01/lean/Main.lean`

## References

- informal-solution: `informal-solution.md`
- Key Mathlib: `AbsolutelyContinuousOnInterval`, `BoundedVariationOn`,
  `tendsto_eVariationOn_Icc_zero_left`, `eVariationOn`

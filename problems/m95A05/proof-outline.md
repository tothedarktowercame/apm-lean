# Proof Outline: m95A05

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95A05.md`

## Compiled progress

- `apm_m95a05_norm_le_apply` derives `c * ‖v‖ ≤ ‖A v‖` from coercivity and
  the continuous-dual operator-norm estimate.
- `apm_m95a05_injective` proves that `A` is injective, closing uniqueness.
- `apm_m95a05_isClosed_range` converts the lower bound into an anti-Lipschitz
  estimate with constant `c⁻¹`, proving the range closed by completeness.

## Remaining boundary

- apply `geometric_hahn_banach_closed_point` to any point outside the now
  proved-closed range and use scalar rescaling to show its separator vanishes
  on the whole linear range;
- transport that double-dual functional through `hrefl` and contradict
  coercivity, proving surjectivity.

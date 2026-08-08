# Proof Outline: m95A05

The frozen theorem is fully proved in Lean.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95A05.md`

## Compiled progress

- `apm_m95a05_norm_le_apply` derives `c * ‖v‖ ≤ ‖A v‖` from coercivity and
  the continuous-dual operator-norm estimate.
- `apm_m95a05_injective` proves that `A` is injective, closing uniqueness.
- `apm_m95a05_isClosed_range` converts the lower bound into an anti-Lipschitz
  estimate with constant `c⁻¹`, proving the range closed by completeness.
- `apm_m95a05_separator_vanishes_on_range` uses scalar rescaling to prove a
  Hahn--Banach separator bounded on the linear range annihilates that range.
- Geometric Hahn--Banach, reflexivity, and coercivity then prove surjectivity;
  injectivity gives the unique solution.

## Remaining boundary

None.

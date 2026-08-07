# Proof Outline: m95A05

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95A05.md`

## Compiled progress

- `apm_m95a05_norm_le_apply` derives `c * ‖v‖ ≤ ‖A v‖` from coercivity and
  the continuous-dual operator-norm estimate.
- `apm_m95a05_injective` proves that `A` is injective, closing uniqueness.

## Remaining boundary

- prove that the bounded-below map has closed range;
- obtain a nonzero continuous functional annihilating any hypothetical proper
  closed range via Hahn--Banach;
- transport that double-dual functional through `hrefl` and contradict
  coercivity, proving surjectivity.

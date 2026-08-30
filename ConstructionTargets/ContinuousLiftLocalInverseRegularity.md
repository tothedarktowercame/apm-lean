# Continuous lift local-inverse regularity

This target proves a generic scalar regularity-transfer theorem. If `theta` is
continuous, `phi ∘ theta` is `C^n`, and `phi` is `C^n` with nonzero derivative
at `theta x`, then `theta` is `C^n` at `x` (for nonzero `n`).

The proof uses Mathlib's local inverse for `phi`, pulls its eventual
left-inverse identity back along continuity of `theta`, and transfers
`ContDiffAt` across the resulting eventual equality. It deliberately contains
no circle-specific or covering-map assertion.

The next seam for `t97J08` is a rotated imaginary-coordinate chart in which
`Circle.exp` has a scalar component with nonzero derivative.

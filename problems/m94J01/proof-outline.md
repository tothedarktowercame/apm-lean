# Proof Outline: m94J01

The Lean artifact proves convergence against compactly supported tests and now
formalizes the oscillation contradiction for the intended Schwartz witness.
One high-order Schwartz interpolation boundary remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94J01.md`

## Formalized

- Compact support eventually excludes every moving center, so the evaluations
  are eventually zero.
- The complex sequence `(-1)^n` cannot converge: subtracting the shifted
  sequence produces a sequence whose norm is constantly two but tends to zero.

## Remaining Boundary

Construct a Schwartz function satisfying
`iteratedDeriv n φ (n : ℝ) = 1` for every `n`. The intended locally finite
sum of translated plateau bumps requires a smooth plateau, local-finiteness
packaging, uniform weighted derivative estimates, and the center derivative
calculation.

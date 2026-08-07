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
- A concrete plateau bump and its normalized translated monomial summands are
  defined.  Eventual equality with the monomial near the center proves the
  exact diagonal identity `iteratedDeriv n summand_n n = 1`.
- `apm_m94J01_localSummand_eq_zero_of_half_le` proves that the `n`th summand
  is supported in the open radius-`1/2` ball around `n`; hence at most one
  summand is active at any point.

## Remaining Boundary

Package the pointwise locally finite sum of the translated plateau-bump
summands as a Schwartz function.  The plateau and center-derivative calculation
are complete, and pointwise finiteness is reduced to uniqueness of an active
index. What remains is local smoothness bookkeeping and uniform bounds for
every weighted derivative seminorm.

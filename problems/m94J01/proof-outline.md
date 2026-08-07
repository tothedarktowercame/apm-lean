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

## Remaining Boundary

Package the pointwise locally finite sum of the translated plateau-bump
summands as a Schwartz function.  The plateau and center-derivative calculation
are complete; what remains is smoothness of the locally finite sum and uniform
bounds for every weighted derivative seminorm.

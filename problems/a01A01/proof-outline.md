# Proof Outline: a01A01

The Lean theorem is present but remains partial with one theorem-level
`sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a01A01.md`

## Formalization route

1. Enumerate partition cells stage-by-stage, using height `sqrt m` and cell
   width small enough that each individual integral tends to zero.
2. Prove the stage associated to a global sequence index tends to infinity.
3. For every point and threshold, choose a sufficiently large stage and the
   unique cell containing that point; prove its global index exceeds the
   requested lower bound.
4. In dimension `d`, tile expanding cubes `[-m,m]^d`; use
   `EuclideanSpace.volume_preserving_measurableEquiv_toLp` and
   `Real.volume_Icc_pi` for the cell-volume calculation.

An ungated historical attempt at commit `2e3057d` contains substantial 1D
helpers but leaves the theorem unfinished. No closed corpus artifact packages
the multidimensional enumeration.

Closer hop 2 repairs and compiles the diagonal pair decoder, its position
bound, the quadratic index bound, and the proof that decoded stages tend to
infinity. It also defines the 1D typewriter cell and proves nonnegativity.
Thus the global-index cofinality component is no longer part of the blocker.

# Proof Outline: m93J05

The frozen Lean theorem is present, but its final stationarity clause is
false because it quantifies over arbitrary directions rather than admissible
`Lᵖ` directions.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93J05.md`

## Statement defect

Take `N = 0`, `p = q = 2`, `g = 1`, and the admissible minimizer
`f₀ = -1/2`. For a non-`L²` direction such as `h(x) = 1/x` on `(0,1]`,
`f₀ + t h` is outside the admissible class for every `t ≠ 0`; moreover the
frozen use of `eLpNorm.toReal` sends an infinite norm to zero. Thus the
displayed real-valued path need not even be continuous at zero and cannot be
required to have derivative zero.

The source's variational equation ranges over directions in `Lᵖ`. The frozen
statement omitted the necessary hypothesis
`MemLp h (ENNReal.ofReal p) μ`. No bridge declaration can truthfully repair
that universal quantifier.

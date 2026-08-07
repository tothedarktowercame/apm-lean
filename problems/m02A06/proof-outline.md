# Proof Outline: m02A06

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A06.md`

## Compiled progress

- Proved positivity of the ball radius `2 * (1 + C)`.
- Derived the strict contraction constant `4 * ε * (1 + C) < 1` from the
  frozen smallness hypothesis.
- Proved the quadratic Lipschitz estimate on the frozen ball.

## Remaining bridge

Construct and bound the half-line Dirichlet Green operator for
`-u'' + u`, including `C²` regularity, the value at zero, decay at infinity,
and its sup-norm estimate. The compiled arithmetic and nonlinear estimate can
then be fed to the standard contraction API.

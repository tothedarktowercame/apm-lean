# Proof Outline: m02A06

The canonical Lean attempt compiles with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m02A06.md`

## Compiled progress

- Proved positivity of the ball radius `2 * (1 + C)`.
- Derived the strict contraction constant `4 * ε * (1 + C) < 1` from the
  frozen smallness hypothesis.
- Proved the quadratic Lipschitz estimate on the frozen ball.
- Defined the explicit half-line kernel
  `G(x,y) = (exp(-|x-y|) - exp(-(x+y)))/2`.
- Proved kernel symmetry, both zero-boundary identities, nonnegativity, and
  the pointwise upper bound `G ≤ 1/2` for nonnegative arguments.

## Remaining bridge

Integrate the now-defined kernel to construct the half-line Dirichlet Green
operator for `-u'' + u`. Split the integral at `y=x` to prove `C²` regularity,
then establish decay and the kernel-mass sup-norm estimate. The compiled
arithmetic and nonlinear estimate can then be fed to the contraction API.

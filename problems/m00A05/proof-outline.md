# Proof Outline: m00A05

The canonical Lean attempt proves existence of an equilibrium by the
intermediate value theorem. Two sorries remain for global well-posedness and
global attraction.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A05.md`

## Formal progress

- `apm_m00A05_lipschitz_vectorField` proves that `x ↦ cos x - x` is globally
  2-Lipschitz.
- The equilibrium in `[0, π/2]` is constructed using the intermediate value
  theorem.
- `ODE_solution_unique_univ` supplies global uniqueness once solutions are
  presented with its derivative conventions.
- `apm_m00A05_hasDerivAt_of_isSolution` converts the frozen interior `deriv`
  equation into exactly that `HasDerivAt` convention.

## Remaining bridges

Globalize Picard–Lindelöf existence to `[0,∞)` and convert its interval
`HasDerivWithinAt` output to `apm_m00A05_isSolution`. For attraction, use global
uniqueness to prevent equilibrium crossing, establish monotonicity, and rule
out a limiting value different from the equilibrium.

Source inspection confirms that Mathlib's Picard constructors remain local;
global existence requires gluing compatible interval solutions. The reverse
conversion from a frozen solution to `HasDerivAt` is complete, so it is no
longer part of the remaining attraction bridge.

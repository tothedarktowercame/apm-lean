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

Closer hop 3 isolates the endpoint issue in uniqueness. Apply
`dist_le_of_trajectories_ODE` on `[δ,t]` for every `δ > 0`; its estimate is
`dist (u t) (v t) ≤ dist (u δ) (v δ) * exp (2 * (t-δ))`. Continuity at zero
and the common initial value make the right side tend to zero as `δ ↓ 0`.
This avoids demanding a derivative at zero, unlike the packaged global and
closed-interval uniqueness theorems. It still does not construct the global
solution required by the first conjunct.

## Hop 4 bridge contract

`apm_m00A05_bridge_global_exists` states precisely the missing globalization:
for every initial value there is one real-function representative satisfying
`apm_m00A05_isSolution` on the full nonnegative half-line. Its proof must glue
the uniformly local Picard solutions and verify continuity at zero plus the
interior derivative equation. The declaration is intentionally unproved and
does not fold the separately identified endpoint-safe uniqueness argument into
the existence contract.

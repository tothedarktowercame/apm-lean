# Proof Outline: t97J05

This bundle has a partial Lean proof with one theorem-level `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J05.md`

## Compiled progress

- `apm_t97J05_f_gamma_eq_value` proves the explicit curve lies in the fiber.
- `apm_t97J05_gamma_mem_parameterTarget` proves it lands in the exact target.
- `apm_t97J05_gamma_injOn` reads injectivity from the first coordinate.
- `apm_t97J05_gamma_surjOn` proves every target point has `q₁ = π/2` and
  `q₂ = 1/q₀`, hence lies on the curve.
- `apm_t97J05_gamma_bijOn` closes the full set-theoretic bijection requested
  by the fifth conjunct.

## Remaining boundary

- Compute the displayed Fréchet derivative and prove its surjectivity.
- Prove smoothness of `gamma` on the positive interval.
- Install the global one-dimensional manifold structure on the full fiber.
- Construct the exact smooth open partial homeomorphisms required by the
  local submersion normal form.

## Hop 4 bridge statements

- `apm_t97J05_bridge_1`: the displayed derivative formula and surjectivity.
- `apm_t97J05_bridge_2`: smoothness of the explicit fiber parameterization.
- `apm_t97J05_bridge_3`: the global one-dimensional manifold structure on
  the actual fiber subtype.
- `apm_t97J05_bridge_4`: the exact pair of smooth open partial homeomorphisms
  realizing the local submersion normal form.

These four facts plus the compiled `apm_t97J05_gamma_bijOn` are exactly the
conjuncts of the frozen theorem.

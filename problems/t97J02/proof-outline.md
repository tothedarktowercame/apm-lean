# Proof Outline: t97J02

The Lean statement uses actual polygon quotients and actual finite covering
maps. One `sorry` remains.

## Compiled progress

- `apm_t97J02_surfaceQuotient` is the canonical disk projection for every
  presentation and is proved continuous and surjective.
- `apm_t97J02_eulerCharacteristic` implements both classification formulas.
- `apm_t97J02_candidate_eulerCharacteristics` verifies all degree-five and
  degree-six candidate genus equations.
- `apm_t97J02_nonorientable_genus_of_euler_eq` proves the general
  nonorientable genus formula `2*n+2` from Euler multiplicativity.
- `apm_t97J02_orientable_genus_of_euler_eq` proves the general orientable
  genus formula `n+1` from the same equation.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J02.md`

## Formal route

- Prove `χ(N₄) = -2` and multiplicativity under finite covers.
- Use closed-surface classification and the orientation-character parity
  obstruction to obtain the exhaustive lists.
- Construct cyclic degree-five and degree-six polygon covers, yielding `N₁₂`
  and `N₁₄`.
- Construct the orientable degree-six cover as a three-sheeted cyclic cover of
  the orientation double cover `Σ₃ → N₄`, yielding `Σ₇`.

## Open boundary

Mathlib has general covering-map definitions but no Euler characteristic for
topological surfaces, finite-cover multiplicativity, orientation-cover
factorization, or compact-surface classification. It also lacks a gluing
theorem that verifies the required explicit maps between these `EqvGen`
polygon quotients are covering maps. Closed artifacts `t01A02`, `t01A04`,
`t03J03`, and `t91A02` do not supply these bridges.

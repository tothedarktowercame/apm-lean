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

## Hop 4 bridge contracts

- `apm_t97J02_bridge_candidate_covers` states the simultaneous construction
  and covering verification of the concrete covers `N₁₂ → N₄`, `Σ₇ → N₄`,
  and `N₁₄ → N₄`.
- `apm_t97J02_bridge_classify_five_and_six_fold_covers` states the exhaustive
  classification of arbitrary connected five- and six-sheeted covers. Its
  proof must combine finite-cover Euler multiplicativity, orientation parity,
  and compact-surface classification with the compiled genus arithmetic.

Both declarations are intentionally unproved. Together they reduce the main
theorem to rearranging conjunctions, without modifying its frozen statement.

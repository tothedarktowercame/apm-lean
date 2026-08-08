# Proof Outline: t91J05

The frozen theorem and a compiling partial development are present.

## Compiled progress

- `apm_t91J05_isFiniteCover_of_homeomorph` proves that the concrete
  finite-cover predicate transports across a homeomorphism of source spaces,
  preserving covering, surjectivity, and finite fibers.
- `apm_t91J05_eulerCharacteristic_odd_genus` proves
  `χ(Σ_(2n+1)) = n * χ(Σ_3)` for the concrete classified-surface data.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t91J05.md`

## Remaining boundary

- prove classification and Euler-characteristic multiplicativity for a
  connected finite cover of the concrete polygon surface;
- construct an actual connected `n`-sheeted cover
  `Surface true (2*n+1) → Surface true 3` for every positive `n`;
- apply the compiled homeomorphism transport to finish the reverse direction.

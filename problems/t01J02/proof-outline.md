# Proof Outline: t01J02

The canonical Lean attempt is `lean/Main.lean`. The induced map's action on
quotient representatives is compiled, and Mathlib's general covering lift API
has been identified.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J02.md`

## Compiled progress

- `apm_t01j02_homotopyMap_mk` rewrites the quotient map on every generalized
  loop representative.
- `IsCoveringMap.existsUnique_continuousMap_lifts` provides the required lift
  of maps from the simply connected cube.

## Remaining boundary

- Prove path connectedness of `Cube.boundary (Fin n)` for `2 ≤ n` and use lift
  uniqueness to show the lifted cube map is constant on the boundary.
- Apply the analogous relative-boundary argument to lifted homotopies.
- Descend lift and projection to inverse functions on the homotopy quotients.

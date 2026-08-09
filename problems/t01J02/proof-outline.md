# Proof Outline: t01J02

The canonical Lean attempt is `lean/Main.lean`. The induced map's action on
quotient representatives is compiled, and Mathlib's general covering lift API
has been identified.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01J02.md`

## Compiled progress

- `apm_t01j02_homotopyMap_mk` rewrites the quotient map on every generalized
  loop representative.
- `apm_t01j02_homotopyMap_id` and `apm_t01j02_homotopyMap_comp` establish the
  expected functorial laws directly by quotient induction.
- `apm_t01j02_homotopyMap_injective_of_boundary_nonempty` proves injectivity
  for a covering map using `IsCoveringMap.homotopicRel_iff_comp`; this removes
  cube-boundary connectivity from the injective half.
- `apm_t01j02_inducedMap_injective` specializes this to `Fin n`, constructs
  the required boundary point from `2 ≤ n`, and handles the basepoint cast.
- `IsCoveringMap.existsUnique_continuousMap_lifts` provides the required lift
  of maps from the simply connected cube.

## Remaining boundary

Hop 4 states the missing topological fact as
`apm_t01J02_bridge_pathConnectedSpace_cube_boundary`: the subtype boundary of
the `Fin n` cube is path connected whenever `2 ≤ n`. The declaration is
intentionally unproved. Once available, uniqueness of covering path lifts
propagates the lifted corner value across the boundary; packaging the lift as
a `GenLoop` and descending to the quotient then completes surjectivity. The
main theorem remains unchanged.

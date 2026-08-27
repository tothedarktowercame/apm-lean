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
- `CubeBoundaryPathConnected.cubeBoundary_pathConnectedSpace` proves the
  required path connectedness of the finite cube boundary.
- `HigherHomotopyCoveringSurjectivity.fin_homotopyMap_bijective` packages lift
  existence, boundary constancy, and relative-homotopy uniqueness.
- `HigherHomotopyCoveringFrozenAdapter.inducedMap_bijective` transports this
  bijection through the frozen basepoint equality.

## Completion

The bridge and final theorem are proved. The frozen definitions and theorem
statements remain unchanged; the final proof unfolds the two induced-map
definitions and applies the promoted frozen adapter.

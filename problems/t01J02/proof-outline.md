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
- `IsCoveringMap.existsUnique_continuousMap_lifts` provides the required lift
  of maps from the simply connected cube.

## Remaining boundary

- For surjectivity, prove connectedness of `Cube.boundary (Fin n)` for `2 ≤ n`
  and use lift uniqueness to show the lifted cube map is constant there.
- Package that lift as a `GenLoop`, project it back, and descend the resulting
  equality to the homotopy quotient.
- Transport the compiled injectivity result across the basepoint equality
  `hbase` in `apm_t01j02_inducedMap`.

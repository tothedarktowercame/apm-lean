# Path connectedness of finite cube boundaries

This target proves the exact topological fact requested by t01J02:
`Cube.boundary (Fin n)` is path connected for `2 ≤ n`.

The proof uses explicit coordinatewise straight paths in the unit interval.
For a boundary point on a zero face, the path goes directly to the all-zero
corner while retaining that zero coordinate. For a point on a one face, a
different coordinate is first set to zero while the one coordinate remains
fixed; the second path then reaches the all-zero corner while retaining the
new zero coordinate. Thus every part of both paths remains literally in
`Cube.boundary`.

`cubeBoundary_pathConnectedSpace` has the same conclusion and hypotheses as
`apm_t01J02_bridge_pathConnectedSpace_cube_boundary`; no covering-map or lift
statement is used.

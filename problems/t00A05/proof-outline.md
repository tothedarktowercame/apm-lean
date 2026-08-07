# Proof Outline: t00A05

The closedness calculation and the unit-circle period are compiled in
`lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t00A05.md`

## Statement-review boundary

The frozen `apm_t00a05_IsC2` predicate does not state that the parametrization
is injective, an embedding, or has winding number one. Its positive signed-area
condition fixes orientation only. An orientation-preserving repeated traversal
retains the image equations and positivity but multiplies the angle-form
period. Consequently the universal `-2π` conclusion is false without a
single-traversal/degree-one hypothesis.

# Proof Outline: t94J06

The compiled lemma `apm_t94J06_boundary_domination` proves that on `‖z‖ = 7`
the entire lower-order term, including `cos ‖z‖`, has norm strictly smaller
than `‖z⁴‖` (using the explicit bound `2059 < 2401`).
The lemma `apm_t94J06_boundary_homotopy_ne_zero` then reuses
`ConstructionTargets.Rouche.rouche_homotopy_ne_zero_on_sphere` to package a
zero-free straight-line boundary homotopy.
Closer hop 2 proves continuity of the full radial/non-holomorphic map and
extracts its boundary nonvanishing as the endpoint of that homotopy.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t94J06.md`

## Remaining boundary

`ConstructionTargets.Rouche` can turn this estimate into a nonvanishing
straight-line boundary homotopy, without needing analyticity.  The remaining
step is topological: the boundary map is homotopic to `z ↦ z⁴`, hence has
degree four, and a continuous zero-free extension over the disk would force
degree zero. Mathlib and repository searches found no winding-number,
Brouwer-degree, or no-retraction theorem packaged in a form that closes this
step for a merely continuous complex-valued map.

The analytic zero-count theorem in `ConstructionTargets.Rouche` cannot be
used because `z ↦ cos ‖z‖` is not holomorphic. The frozen statement is
unchanged and appears sound.

# t01J03 frozen quotient representation

This target isolates the definition-for-definition representation change
between the coordinate solid tori used by frozen `t01J03` and
`SolidTorusGluingOpenCover`.

It provides coordinate solid-torus and boundary-torus types, their explicit
homeomorphisms to the reusable types, compatibility of the boundary
inclusions, conjugation of an arbitrary boundary homeomorphism, and the
piecewise sum homeomorphism.  `coordinateGlueRel_iff_boundaryGlueRel` and
`coordinateEqvGen_iff_boundaryEqvGen` prove relation compatibility rather than
assuming it.  `coordinateGluingHomeomorph` then descends the piecewise
homeomorphism through both quotients, proves continuity from their coinduced
topologies, and supplies computation rules on canonical representatives.

The frozen problem is not an importable Lake module.  The remaining local
consumer step in `problems/t01J03/lean/Main.lean` is to identify
`apm_t01J03_glueRel` with `CoordinateGlueRel` (their coordinate types and
boundary inclusions are definition-for-definition identical), descend that
identity through `EqvGen`, and compose with `coordinateGluingHomeomorph`.
This target does not assert that frozen-local identification, a homology
calculation, or the final `t01J03` conclusion.

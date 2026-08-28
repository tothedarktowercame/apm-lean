# t96A03 frozen quotient representation

This target proves the representation change that can live upstream of the
frozen problem:

- `coordinateEquatorHomeomorph` identifies the frozen nested subtype with
  `sphereEquator 2`, including the `Fin.last 2 = 2` normalization;
- `conjugateEquatorHomeomorph` transports an arbitrary gluing map;
- `coordinateGlueRel_iff_equatorGlueRel` and
  `coordinateEqvGen_iff_equatorEqvGen` prove literal agreement of the generator
  and generated relations;
- `coordinateGluingHomeomorph` descends the identity on sphere-sum
  representatives through those relations and proves continuity in both
  directions from the coinduced quotient topologies.  Its `_mk` theorem is the
  canonical-inclusion computation rule.

The frozen file is not an importable Lake module (`import
problems.t96A03.lean.Main` reports `unknown module prefix 'problems'`).  Thus a
ConstructionTarget cannot mention `apm_t96A03_X` directly.  The remaining
consumer step belongs in the frozen file after importing this target: identify
`apm_t96A03_glueRel` with `CoordinateGlueRel`.  After that definitional
adapter, `coordinateGluingHomeomorph` is the required quotient homeomorphism.
No frozen equality or homology conclusion is asserted here.

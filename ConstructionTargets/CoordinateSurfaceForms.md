# Alternating coordinate forms and parameter integrals

Coordinate wedges are determinants composed with coordinate projections, bundled as continuous alternating maps. volumeForm is the actual three-dimensional determinant. pullbackCoefficient evaluates a two-form on both parameter derivatives; rectangleIntegral integrates it with the stated parameter orientation. This is a defined parameter-integration operation, not a full arbitrary-manifold integration theory. A consumer must identify the geometric image and coverage/orientation. t99J06 includes those construction certificates in its conclusion.

Consumers: t99J06.

Validation: `lake build ConstructionTargets.CoordinateSurfaceForms`; the module is imported by
`ConstructionTargets.lean` and has an `.olean` in the library build directory.
All definitions and the elementary construction proofs in this module are
free of `sorry`; the consuming problem theorems remain explicitly unproved.

# Concrete polygon surfaces and circle wedges

Provides the disk-quotient real projective plane and Klein bottle, an iterated three-circle wedge, and explicit product-of-commutator presentations. All quotient topologies come from existing Surfaces and PointWedgeQuotient definitions. No fundamental-group identification is postulated.

Consumers: t93J03, t96A01, t96A02, t96J02, t99J01.

Validation: `lake build ConstructionTargets.StatementSurfaceModels`; the module is imported by
`ConstructionTargets.lean` and has an `.olean` in the library build directory.
All definitions and the elementary construction proofs in this module are
free of `sorry`; the consuming problem theorems remain explicitly unproved.

# The exact smooth-projective construction requirement

The sphere projection is a concrete function into ProjectiveSpaceTopology.Space. SmoothAtlas packages charts on that specified topology, IsManifold, and the assertion that that specific sphere projection is a local diffeomorphism. The module does NOT construct a SmoothAtlas inhabitant. Consumers explicitly existentially quantify its construction in their theorem conclusion. No consumer embedding or transversality conclusion appears as a field, so the target does not assume the problem it is meant to support.

Consumers: t95A04, t96A07.

Validation: `lake build ConstructionTargets.RealProjectiveSmoothTarget`; the module is imported by
`ConstructionTargets.lean` and has an `.olean` in the library build directory.
All definitions and the elementary construction proofs in this module are
free of `sorry`; the consuming problem theorems remain explicitly unproved.

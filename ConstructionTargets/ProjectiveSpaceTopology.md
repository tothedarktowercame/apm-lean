# Projectivization with its quotient topology

Wraps Mathlib Projectivization in a separate Space type and equips it with the coinduced topology from nonzero coordinate vectors. Proves continuity and surjectivity of the concrete projection. This does not install a global competing topology instance on Mathlib Projectivization. No smooth atlas or homology computation is claimed.

Consumers: t96A06, t95A04 and t96A07 through RealProjectiveSmoothTarget.

Validation: `lake build ConstructionTargets.ProjectiveSpaceTopology`; the module is imported by
`ConstructionTargets.lean` and has an `.olean` in the library build directory.
All definitions and the elementary construction proofs in this module are
free of `sorry`; the consuming problem theorems remain explicitly unproved.

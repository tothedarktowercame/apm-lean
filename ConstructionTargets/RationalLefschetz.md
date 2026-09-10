# Rational singular-homology invariants

HasLefschetzNumber is a predicate over actual induced rational singular-homology endomorphisms. It requires finite dimensionality in every degree, eventual vanishing, and the alternating-trace equation. It does not use the default zero trace of an infinite-dimensional space as a fake invariant. HasEulerCharacteristic uses the identity map. Existence, uniqueness/bound-independence lemmas, computations and fixed-point theorems remain future work; no such theorem is assumed here.

Consumers: t96A06, t98J01.

Validation: `lake build ConstructionTargets.RationalLefschetz`; the module is imported by
`ConstructionTargets.lean` and has an `.olean` in the library build directory.
All definitions and the elementary construction proofs in this module are
free of `sorry`; the consuming problem theorems remain explicitly unproved.

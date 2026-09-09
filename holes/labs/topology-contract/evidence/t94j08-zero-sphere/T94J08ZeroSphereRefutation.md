# t94J08: compiled refutation of the frozen statement — 2026-09-09

STOP: mathematical refutation of the frozen encoding, not missing infrastructure.

T94J08Sphere k is the unit sphere in EuclideanSpace real (Fin k). Consequently
T94J08Sphere (0+1) is S0, not S1. T94J08TopHomology 0 uses ordinary integral
H0. The frozen orientation requirement therefore asks for H0(S0) isomorphic
to Z. That is impossible.

The fixture /tmp/T94J08ZeroSphereRefutation.lean preserves the original proved
prefix, imports banked SphereAntipodalHomology, and proves two statements:

- diagnostic_no_zero_orientation: no such ModuleCat orientation exists.
- diagnostic_refutes_frozen_theorem: the literal negation of the complete
  frozen apm_t94j08 proposition, copied without changing its binders or clauses.

The first proof uses directDiscreteH0Iso in ModuleCat Z, the actual categorical
coproduct/direct-sum comparison, and invariance of module finrank under a linear
isomorphism. The sphere has two explicitly distinct points, so its finite
cardinality exceeds one; the H0 direct sum has that rank, whereas Z has rank one.
The second proof specializes the first conjunct of the frozen proposition to
n=0 and extracts the impossible orientation. Neither frozen sorry-bearing theorem
is included or imported. Both proofs compile with standard axioms only.

This directly contradicts TOPOLOGY-DEPENDENCY-DAG.md's statement that using
T94J08Sphere (n+1) avoids the ordinary-H0 defect. That index is the ambient
dimension, so the zero-sphere case remains. No DAG or source edit was made.

The unmodified positive-dimensional orientation theorem in SphereHomology
requires 0<n. The reduced zero-sphere oriented-difference result in
SphereAntipodalHomology is compatible with the usual degree convention, but
cannot supply an isomorphism from the entire ordinary H0 to Z.

A structural repair could use reduced homology in degree zero (preserving the
intended low-dimensional index problem), or explicitly restrict the theorem's
scope to positive sphere dimension and adjust its local-index clause. Neither
repair is implemented or adopted here; the frozen theorem cannot be proved.

Validation: lake env lean on the fixture exits 0. Axioms for both refutations:
propext, Classical.choice, Quot.sound. Warnings: three inherited prefix lints
and unused hv/hp/hr in the copied negated proposition. The consumer remains
unchanged with two executable placeholders. Refutation is of this encoding,
not of the classical antipodal-degree theorem or Sard.

# OrientedSurfacePreimageDuality

This module fixes the exact reusable interface still missing from the
transverse-preimage argument for `t00J02`: Poincare duality for a compact,
connected, charted two-manifold must turn operational derivative
transversality into `TransversePreimageDuality.DetectsTopMap` for integral
singular homology in degrees one and two.

`Producer` is deliberately independent of genus computations, essentiality of
the embedded circle, and disk fillings.  Those hypotheses are consumed by
`DiskBoundedPreimageDuality`; mixing them into the geometric producer would
make the interface unusable by other surface arguments.

`topHomologyMap_eq_zero_of_producer_and_componentsBoundByDisks` is the
end-to-end eliminator.  It composes the producer with operational
transversality, the standard cyclic-domain monomorphism argument, and the
disk-bounded null-winding theorem.  Thus consumers need not reconstruct the
categorical chain locally.

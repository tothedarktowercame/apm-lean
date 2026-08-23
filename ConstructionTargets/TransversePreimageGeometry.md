# TransversePreimageGeometry

This module provides the reusable adapter at the remaining `t00J02` geometry
seam.  `HoldsAlong` records a pointwise geometric condition along an incidence
relation without forcing tangent spaces to be definitionally constant.
`detectsTopMap_of_pointwise_condition` feeds such a condition directly to a
consumer-supplied transverse-preimage duality producer.

The module intentionally does not assert Poincare duality from transversality:
that is the remaining manifold-specific theorem.  It makes the exact input and
output of that theorem stable and reusable without depending on a particular
manifold chart model.

# Convert extended-distance separation to a real-distance bound

`IsSeparated.real_dist_le` bridges the two distance representations used by the
Sard packing argument.  From Mathlib's `ENNReal`-valued `Metric.IsSeparated`
predicate on the image of a finite family of centers, it derives
`(ε : ℝ) ≤ dist (c i) (c j)` whenever the two center images are distinct.

This adapter does not extract the maximal separated family, prove its packing
cardinality estimate, or apply the Taylor target-volume exponent.  The
remaining Sard obligation is one finite-dimensional polynomial packing bound
and Taylor target-volume exponent estimate, before local rank reduction.

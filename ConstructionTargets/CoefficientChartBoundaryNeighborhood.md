# Actual chart boundary and nearby-point neighborhood

The module constructs a sphere boundary inside the translated common source of two actual charts. M is Type 0 and charted on EuclideanSpace ℝ (Fin (m+2)); x belongs to both chart sources. R is any Type 0 commutative ring. This geometric construction needs no separation assumption on M; relative neighborhood excision retains its separate Hausdorff hypotheses.

`radius_exists` uses openness and zero membership of the translated image to obtain an open ball, then halves its radius so the closed ball lies in that image. `radius` chooses this positive radius, with positivity and containment proved. `sphereBoundary` is literally z ↦ radius • z from the unit sphere into the translated image, with membership and continuity proved.

`sourceBoundary` returns this sphere to the actual common chart source. `source_member` proves membership in both charts. `mappedBoundary` applies the actual translated transition; `mapped_formula` identifies its value as chart_b(sourceBoundary(z)) - chart_b(x). Its avoidance of zero follows from actual deleted-zero transition preservation and the positive radius.

`boundary_neighborhood` applies the compact-boundary center-motion theorem to this mapped sphere. It constructs an open V containing x inside the common source by intersecting the strict source-radius condition with the target separation condition. Every y in V has source coordinate displacement strictly smaller than the radius, and the actual mapped boundary recentered at chart_b(y)-chart_b(x) induces the same coefficient homology map as at zero in every natural degree. Openness uses continuity on the actual chart sources. Integer and rational chart examples and eight standard-only axiom audits are included.

The Lean source exactly matches fixture SHA256 00f467857529fd6d33f1ba79eee6f4aebdfa9d6c1ae7f5aafbb01c06a1e20d29. No radius, boundary map, orientation or compatible local generator is supplied.

The source and mapped boundary maps still require identification with relative local-homology normalizations through connecting naturality, radial normalization and neighborhood inclusion. Equality of transition units at nearby points, orientation compatibility and consumer closure remain downstream; this module establishes only the stated absolute homology comparison.

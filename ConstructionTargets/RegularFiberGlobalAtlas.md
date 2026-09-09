# Global regular-fiber atlas

For globally genuine-infinity ContDiff f between finite-dimensional real
normed spaces E and F, with E complete, and a regular value c,
`exists_manifold` constructs ChartedSpace and IsManifold genuine infinity on
{x : E // f x = c}. The model is EuclideanSpace real
(Fin (finrank E - finrank F)). The topology is the existing subtype topology;
no replacement topology is defined or installed.

`selected` chooses the actual chart family constructed by
RegularFiberFixedModelOverlaps.exists_cover. `selected_center` proves that
every point belongs to its selected chart source. `chartedSpace` uses the
range of this family as its atlas and the selected chart as chartAt.
`chartAt_eq`, `atlas_eq` and `selected_mem_atlas` give exact specifications.

`isManifold` applies Mathlib's isManifold_of_contDiffOn. Membership in the
range atlas yields the two actual fiber points indexing each chart. The
banked overlap_smooth theorem gives smoothness of their actual transition on
its source. The self model has identity coordinates and full range, so the
model-coordinate compatibility obligation simplifies to precisely that
transition theorem. No chart, coverage or compatibility is supplied as a
premise, and no local implicit-function construction is duplicated.

Empty fibers are covered without selecting a nonexistent point: the selected
family is indexed by the fiber itself, and coverage and compatibility are
vacuous when it is empty. Zero-dimensional kernels use the same Euclidean
model and proof. There are no nonempty, nontrivial or positive-dimensional
hypotheses.

The result supplies the global atlas for Euclidean-source regular fibers.
Smooth embedded inclusion and the manifold tangent-image equality remain,
as do manifold-source transport and frozen consumer uptake. It does not
claim orientation, an embedded inclusion theorem or t96J05 closure.

Preserve all prior APIs. Implementation promotes only this documentation and
RegularFiberGlobalAtlas.lean. Validation comprises a warning-free direct Lean
compile, six standard-only axiom audits, and a zero-placeholder check.

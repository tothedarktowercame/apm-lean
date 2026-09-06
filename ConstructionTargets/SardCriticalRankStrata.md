# Finite rank-stratum decomposition of a critical set

This target defines `criticalSet` as the nonsurjective locus of a family of
linear maps `E →ₗ[ℝ] F` and `rankStratum` as the locus where the range has a
specified finite rank.  When `F` is finite-dimensional,
`criticalSet_eq_iUnion_rankStratum` identifies the critical set with the union
indexed by `r : Fin (finrank ℝ F)` of these exact-rank strata.

The result is purely finite-dimensional linear algebra.  For a derivative
family it converts nonsurjectivity into finitely many exact derivative-rank
loci, but proves no regularity or image-nullity for those loci.  The remaining
rectangular Sard obligation is one uniform C∞ rank-stratum image-nullity
theorem; manifold chart assembly remains outside this target.

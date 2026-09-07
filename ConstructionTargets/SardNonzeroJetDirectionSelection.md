# Nonzero-jet direction selection

This module promotes the pointwise direction-selection step for the nonzero
pieces of the higher-jet decomposition.

A continuous multilinear map is zero exactly when it evaluates to zero on
every tuple of input directions.  Therefore a nonzero `i`-multilinear map has
some tuple `v : Fin i → E` on which its value is nonzero.  The second theorem
specializes this directly to `iteratedFDeriv ℝ i f x`, without changing the
jet representation used by the preceding decomposition and open-locus
modules.

This selection is pointwise and makes no continuity claim about the chosen
directions.  The next step is to separate the selected nonzero target value by
a scalar functional and prove the derivative formula for the resulting
fixed-direction jet component.  That scalar component can then supply the
implicit-function hypersurface used in source-dimension reduction.

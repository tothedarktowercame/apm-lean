# Local residual derivative flatness

This module promotes the neighborhood-wise residual-flatness theorem while consuming the preceding projected-kernel theorem directly.

On a locus where the fixed projected derivative block is surjective and the full derivative rank is bounded by the projected target dimension, `apply_eq_zero_of_mem_projected_ker` shows that the full derivative kills every direction tangent to the projected fibre. Any residual target projection therefore also has zero derivative in that direction.

The next consumer step is to instantiate the derivative field with `fderiv f`, choose the complementary target projection, transport this vanishing through the local partial homeomorphism to kernel-coordinate slices, then apply Taylor-cover nullity and perform the rank/source-dimension induction.

# Uniform flat Taylor remainder on a bounded locus

This module promotes the compiled theorem `exists_uniform_flat_taylor_remainder_on_bounded_set`.

A bounded locus is placed inside a closed ball, compact by `ProperSpace` and convex for every segment between locus points. Compactness supplies one bound `D` for the order-`k + 1` iterated Fréchet derivative. The affine-line derivative estimate scales this by `‖x - a‖^(k + 1)`, while vanishing derivatives through order `k` collapses the Taylor polynomial. Dividing `D` by `k!` produces one nonnegative remainder constant valid for every pair of points in the locus.

The next consumer residual is to instantiate `exists_taylor_cover_measure_lt` with this uniform remainder constant and derive the complete arbitrarily-small image-measure/nullity theorem; local rank reduction remains after that composition.

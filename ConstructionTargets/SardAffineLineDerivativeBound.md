# Affine-line iterated-derivative bound

This module promotes the arbitrary-parameter affine-line derivative identity and its convex-set norm estimate from the compiled fixture.

`iteratedFDeriv_affineLineRestriction_at` identifies every iterated derivative of `t ↦ f (a + t • v)` with the ambient iterated Fréchet derivative composed slotwise with the scalar-line map. `affineLine_iteratedDerivWithin_norm_le` uses convexity to keep the segment inside the set carrying the ambient derivative bound, then applies the norm estimate for slotwise composition. The resulting factor is exactly `‖x - a‖ ^ n`.

The next consumer residual is to apply compact derivative boundedness on a compact convex container for the bounded locus, instantiate this affine-line estimate at order `k + 1`, absorb the factorial into a uniform remainder constant, and compose with `exists_taylor_cover_measure_lt`.

# Lower-dimensional ambient image nullity

`lowerDimension_ambient_image_zero` proves zero additive Haar measure of the
entire image `f '' s` for finite-dimensional real normed spaces when the source
finrank is strictly smaller than the target finrank. The target is Borel, and
`f` is ambient differentiable at every point of the arbitrary source set `s`.

The proof constructs a surjection from target to source in finite-basis
coordinates. Coordinate restriction is surjective by extension with zeros;
the basis equivalences transport it to a linear map between the original
spaces. Finite-dimensional continuity turns it into a continuous linear map.
The reviewed `image_zero_of_lower_dimension_surjective_lift` then supplies
image nullity. This discharges its supplied-map premise internally.

No source measurable structure or measure, openness or measurability of `s`,
derivative continuity, or supplied nullity certificate is required. Ambient
differentiability and the strict dimension inequality remain essential premises.

The Lean file matches `/tmp/SardLowerDimensionAmbientImageNullityProbe.lean`,
SHA-256 `aa20804c0056b546893ab395e11ec125840ca5281a0e4b113869f2c60480331c`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The observed dependency is the surjective-lift module. Intended consumers are
t93A04 and, through the shared Sard foundation, t01A08, t01J04, t92J07, and
t96J05; no frozen consumer is closed by this module. Remaining low-order
assembly and the complementary-overlap analytic premise must be discharged
before rectangular closure and subsequent manifold assembly. The frozen
consumer and ledger are unchanged.

The boundary for this construction would be failure of coordinate
surjectivity, finite-dimensional continuity, reviewed lift nullity under the
stated hypotheses, or a requirement for nonstandard axioms.

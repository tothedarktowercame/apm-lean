# Local endpoint compact cover data

`localEndpoint_coverData_of_compact_remainder` constructs
`LocalEndpointSmallCoefficientCoverData` for a compact bounded source locus.
Its inputs include a nonnegative Taylor coefficient valid for pairs at distance
less than a positive radius, and the coefficient expression below the requested
target tolerance. The source unit-ball volume constant is assumed nonzero.

The proof chooses scale `min 1 (δ / 2)`, obtains a maximal separated finite
cover with its packing-cardinality bound, and uses containment of its centres
in the locus to establish all localized remainder estimates.

This construction does not derive the coefficient from smoothness or flatness.
Arbitrarily small uniform Taylor coefficients and positive validity radii on
compact flat loci remain the analytic input needed for endpoint nullity.

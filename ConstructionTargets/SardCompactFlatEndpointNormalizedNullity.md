# Normalized compact flat endpoint nullity

`compact_flat_endpoint_volume_eq_zero_normalized` proves zero image volume
for a compact locus flat through order k+1 under global C^(k+1) regularity
and exact equality `(k + 1) * finrank F = finrank E`.
The real inner-product source and target are nontrivial and finite
dimensional with Borel measurable structures; `ProperSpace E` is retained.

The proof consumes `compact_flat_endpoint_volume_eq_zero` from
`SardCompactFlatEndpointNullity`. It constructs an enclosing closed ball
from compactness and proves the source unit-ball constant positive using
positivity of the square root of pi, its natural power, and Gamma at
`finrank E / 2 + 1`. Thus neither bounding-ball data nor a nonzero volume
normalization is a separate input to this theorem.

The source is byte-identical to the accepted fixture
`/tmp/SardCompactFlatEndpointNormalizedNullityProbe.lean`, SHA-256
`75f7ecfd92907ea27aec2208544487f769d6cb566b8a98840cbcfb28c4df7a26`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The intended consumer is t93A04. Other proposed consumers are t01A08,
t01J04, t92J07, and t96J05; no frozen consumer is changed or closed here.
The remaining work is finite-order jet specialization, localization,
induction, and compact exhaustion.

The stop boundary is failure of compact boundedness or positivity of the
source unit-ball constant, or a need for nonstandard axioms, not missing
downstream assembly.

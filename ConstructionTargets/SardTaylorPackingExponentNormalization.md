# Taylor packing exponent normalization

`ENNReal.raw_taylor_packing_product_le` combines the raw finite-dimensional
packing factor and the order-`k + 1` Taylor target-ball factor. Under
`0 < r ≤ 1`, nonnegativity of the Taylor constant, and the Morse--Sard exponent
equation `(k + 1) * n = m + d`, their product is bounded by a scale-independent
constant times `ENNReal.ofReal r ^ d`.

The theorem preserves the fixture's exact real and ENNReal factors. It uses the
promoted exponent-combination theorem and only standard axioms.

The remaining consumer work is to instantiate the maximal-separated cover at
geometric radii, combine its cardinality and finite target-cover measure bounds
through this normalization theorem, and choose the radius using positive-power
tolerance.

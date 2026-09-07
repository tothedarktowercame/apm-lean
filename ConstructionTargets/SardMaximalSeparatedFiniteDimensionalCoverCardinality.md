# Maximal-separated finite-dimensional cover cardinality

`exists_finiteDimensional_maximalSeparated_cover_card_le` extracts a finite
maximal separated family from a compact set, retains containment and covering,
converts ENNReal separation to a real-distance bound, and applies the reviewed
finite-dimensional packing estimate. Its cardinality is bounded by
`ofReal ((2 * R + ρ) / ρ) ^ finrank ℝ E`.

The theorem preserves the compiled fixture's compactness, separation,
boundedness, and volume-constant hypotheses. Remaining work is to apply Taylor
control on the covered source balls, aggregate target-ball volumes, cancel the
source dimension against the Taylor exponent, and choose a geometric scale.

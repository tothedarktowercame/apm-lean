# Compact flat nonnegative-budget nullity

`compact_flatThrough_image_zero_of_nonnegative_budget` proves zero target
add-Haar measure of the image of `flatThrough f K (k + 1)` whenever K is
compact, f is globally C^(k+1), and `finrank E ≤ (k + 1) * finrank F`.
The source and target are nontrivial finite-dimensional real inner-product
spaces with Borel measurable structures; `ProperSpace E` is retained.

Equality uses `SardLocalizedFlatThroughEndpointNullity`. Strict inequality
uses `SardLocalizedFlatThroughAddHaarNullity` with positive surplus equal
to the dimension difference. Compactness supplies the enclosing ball;
positivity of pi and Gamma supplies source volume normalization, and the
contraction is 1/2. The strict theorem gives nullity for the order-k flat
locus. The order-(k+1) locus is a subset, so image monotonicity gives the
stated conclusion without changing derivative orders.

These two modules are observed dependencies. The source is byte-identical
to `/tmp/SardCompactFlatNonnegativeBudgetNullityProbe.lean`, SHA-256
`7f43fd8adcff6518a857751b4a9069d3a4cb6260b6c8560cd578c6dbebda83e5`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

The intended consumer is t93A04. Other proposed consumers are t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is changed or closed here.
Remaining work is to instantiate finite-order admissibility, discharge the
non-flat jet branches, and complete local induction and exhaustion.

The stop boundary is failure of the strict/equality split or the flat-locus
containment, or a need for nonstandard axioms. Missing downstream assembly
is not a refutation.

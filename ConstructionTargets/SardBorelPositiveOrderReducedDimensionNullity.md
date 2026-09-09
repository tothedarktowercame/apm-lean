# Borel positive-order reduced-dimension nullity

`reducedDimension_slice_nullity_of_borel_positive_order` instantiates positive-order critical-image induction on a smaller-dimensional slice. The slice source and target are finite-dimensional real normed spaces; only the target requires a Borel measurable structure and an additive Haar measure.

The source and target dimension identities subtract the same rank from the original dimensions. The explicit bounds on that rank allow the reviewed rank-drop admissibility theorem to preserve classical admissibility. The finite regularity order is unchanged, so the supplied hypothesis `1 ≤ order` applies directly at the induction call. Pointwise ambient regularity on an arbitrary source subset suffices; no source measure or measurability of that subset is assumed.

This theorem consumes `BorelPositiveOrderCriticalNullityAtDimension` below the dimension bound. It neither proves that induction hypothesis nor converts it into the broader all-orders predicate. The latter remains unchanged.

## Verification

The Lean source reproduces `/tmp/SardBorelPositiveOrderReducedDimensionNullityProbe.lean`, SHA-256 `7cd3db8b4b0c6a07f51e370f3f4ae25d6f0281eda9bb444f9cb0fa888fb3624c`. The declaration's axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining consumer work

Integrate this interface into positive-rank chart nullity and the positive-order jet theorem into rank-zero aggregation, then resolve complementary analytic cases before rectangular closure. The frozen smooth consumer is unchanged; this module does not close rectangular Morse–Sard.

# Finite-order higher-jet variable induction

`higher_firstNonzeroJetLoci_null_of_remainingOrder_induction` proves nullity
of first-nonzero-jet locus images for orders 2 through k+1, given global
C^(k+1) regularity, criticality on K, and explicit lower-dimensional nullity
hypotheses at remaining orders k+1-i for every 1 <= i <= k.

The source is a finite-dimensional complete second-countable real
inner-product space. The target is a real inner-product space with a
measurable structure, and the target measure is arbitrary. No compactness
or add-Haar hypothesis is needed for this conditional theorem.

For j=i+1 in the stated range, the natural remaining order is positive and
finite. Its sum with i is k+1. These facts supply the smoothness premises of
the banked single-locus induction theorem, consumed through
`SardHigherFirstNonzeroJetLociInduction`. Natural subtraction is performed
before casting to `WithTop ℕ∞`.

The lower-dimensional nullity hypotheses remain assumptions. This theorem
does not show that classical Sard admissibility supplies them. Determining
how to discharge them is the next mathematical task before compact rank-zero
assembly and localization can close the consumer.

The source is byte-identical to the accepted fixture
`/tmp/SardFiniteOrderHigherJetVariableInductionProbe.lean`, SHA-256
`c887d2994533c0117d2c4fc57e3e11a1cbf501f97c246f1e5af16fd380ee5a00`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
The intended consumer is t93A04, with t01A08, t01J04, t92J07, and t96J05
as additional proposed consumers. No frozen consumer is changed or closed.

The stop boundary is failure of the remaining-order arithmetic or of
single-locus aggregation under the explicit hypotheses, or a need for
nonstandard axioms; missing downstream induction is not a refutation.

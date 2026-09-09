# Compact rank-zero admissible jet assembly

`compact_rankZero_image_zero_of_admissible_higherJets` proves zero add-Haar
measure of the image of a compact rank-zero locus, conditional on image
nullity of its first-nonzero-jet loci of orders 2 through k+1.
The map is globally C^(k+1), and classical admissibility means
`sourceDim < targetDim + (k + 1)`. Source and target are nontrivial
finite-dimensional real inner-product spaces with Borel structures;
`ProperSpace E` is retained.

The proof consumes four reviewed modules: `SardCompactFlatNonnegativeBudgetNullity`,
`SardFiniteOrderTaylorBudgetEndpoint`, `SardFiniteOrderRankZeroFirstJetEmpty`,
and `SardFirstNonzeroJetFiniteAssembly`. Admissibility supplies the
nonnegative Taylor budget and hence flat-through nullity. Rank zero makes
the first-jet locus empty. Finite assembly combines these with the explicit
higher-jet hypotheses, preserving their exact index range and image sets.

This is an assembly theorem, not an unconditional Morse-Sard theorem.
The higher-jet nullity hypotheses still need finite-order lower-dimensional
induction. Localization and exhaustion also remain.

The source is byte-identical to the accepted fixture
`/tmp/SardCompactRankZeroAdmissibleJetAssemblyProbe.lean`, SHA-256
`4852d51636100f521d4f9ea12cad61460f612a21f8889977d866a23c013f8589`.
Its axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.
The intended consumer is t93A04; additional proposed consumers are t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is changed or closed here.

The stop boundary is failure of the admissibility implication, first-jet
elimination, or finite covering by the null branches, or a need for
nonstandard axioms. Missing induction infrastructure is not a refutation.

# Closed-open C1 parameterized flat nullity

`closed_inter_open_C1_parameterized_flat_image_addHaar_eq_zero` proves zero
target add-Haar measure of `(f ∘ p) '' (s ∩ U)`, where s is closed and U is
open in parameter space. The parametrization p is C1 at every point of U.
The ambient map f is globally C^(k+1), with derivatives of orders 1 through
k vanishing at every p(a) for a in s ∩ U. The strict dimension hypothesis is
`parameterDim < (k+1)*targetDim`.

The parameter and target spaces are nontrivial finite-dimensional real
inner-product spaces with Borel structures. The parameter space is proper
and second countable; the ambient space is a proper real normed space.
Neither compactness of s ∩ U nor an explicit Lipschitz constant is assumed.

The observed dependencies are `SardClosedOpenImageNullity` and
`SardCompactLipschitzParameterizedFlatNullity`. Closed-open exhaustion
reduces the conclusion to compact parameter subsets K. Pointwise C1
regularity supplies Lipschitz bounds on neighborhoods, hence local
Lipschitz continuity on K. Compactness supplies one Lipschitz constant on
K, and the compact parameterized theorem supplies its image nullity.
All flatness and regularity hypotheses are restricted in the direction
K ⊆ s ∩ U before invoking compact nullity.

The intended consumer is t93A04; other proposed consumers are t01A08,
t01J04, t92J07, and t96J05. Applicable jet loci still need representation in
closed-open parameter coordinates, together with chart regularity and
flatness. Jet cases outside the strict dimension range remain unresolved
before rectangular induction. This theorem does not infer automatic
remaining-order admissibility or close a frozen consumer.

The source is byte-identical to the accepted fixture
`/tmp/SardClosedOpenC1ParameterizedFlatNullityProbe.lean`, SHA-256
`4ad23802ce7059d72c23d76e98eb2a7090523e2225aafb1579dedc4f7f1438a2`.
Its declaration uses only propext, Classical.choice, and Quot.sound.
The stop boundary is failure of compact Lipschitz localization or
closed-open nullity aggregation under the stated hypotheses, or a need
for nonstandard axioms.

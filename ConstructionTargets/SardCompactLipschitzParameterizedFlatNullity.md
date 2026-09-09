# Compact Lipschitz parameterized flat nullity

`compact_lipschitz_parameterized_flat_image_addHaar_eq_zero` proves zero
target add-Haar measure of `(f ∘ p) '' s`. The parameter set s is compact,
p is Lipschitz on s, and the ambient map f is globally C^(k+1) with
derivatives of orders 1 through k vanishing on p(s). The strict dimension
condition is `parameterDim < (k+1)*targetDim`, not an ambient-dimension bound.

Parameter and target spaces are nontrivial finite-dimensional real
inner-product spaces with Borel structures; the parameter space is proper.
The ambient space is a proper real normed space. No differentiability or
injectivity of p is required. The theorem does not infer smoothness of the
composite or automatic remaining-order Sard admissibility.

Compactness supplies a parameter bounding ball and, using Lipschitz
continuity, an ambient bounding ball for p(s). The observed dependency
`SardLipschitzParameterizedFlatTaylorRemainder` supplies the composite's
uniform remainder bound. Positivity of pi and Gamma discharges the parameter
unit-ball normalization. `SardQuantitativeTaylorCoverMeasure` constructs
finite covers at arbitrarily small inverse-natural tolerances with geometric
scale 1/2. `SardArbitrarilySmallMeasureLimit` yields volume nullity, and
`SardVolumeNullityToAddHaar` transfers it to the supplied target measure.

The intended consumer is t93A04; additional proposed consumers are t01A08,
t01J04, t92J07, and t96J05. Constructing localized Lipschitz chart restrictions
and compact parameter subsets for the applicable jet loci remains. Higher-jet
cases outside the strict dimension range still require analytic repair before
induction and exhaustion. No frozen consumer is changed or closed here.

The source is byte-identical to the accepted fixture
`/tmp/SardCompactLipschitzParameterizedFlatNullityProbe.lean`, SHA-256
`0fd0e7e5d0f3295c664b9bdd97961b6b7471796e95829ce08eb6bfb493c1e9b2`.
The declaration uses only propext, Classical.choice, and Quot.sound.
The stop boundary is failure of compact image nullity under the stated
Taylor and strict dimension hypotheses, or a need for nonstandard axioms.

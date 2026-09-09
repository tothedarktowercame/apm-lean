# C1 parameterized flat locus nullity

`C1_parameterized_flat_locus_image_addHaar_eq_zero` proves zero target
add-Haar measure of the composite image of the exact parameter subset
where ambient derivatives of orders 1 through k vanish. The ambient map
is globally C^(k+1), and the parametrization is C1 at every point of an
open parameter set U. The strict bound is
`parameterDim < (k+1)*targetDim`.

Parameter and target spaces are nontrivial finite-dimensional real
inner-product spaces with Borel structures. Parameter space is proper and
second countable; ambient space is a proper real normed space. Global
continuity of the parametrization, a closed parameter-locus certificate,
compactness, and an explicit Lipschitz constant are not assumed.

Derivative continuity makes the ambient flat locus Z closed, as an
intersection of derivative zero sets. C1 regularity implies continuity
on U. Mathlib's `continuousOn_iff_isClosed` supplies a closed set s with
`p ⁻¹' Z ∩ U = s ∩ U`; this does not assert that the full preimage is
globally closed. The proof identifies the exact parameter locus with this
intersection and applies the observed dependency
`SardClosedOpenC1ParameterizedFlatNullity`, preserving the orientation of
the equality and the flatness hypotheses.

The intended consumer is t93A04; other proposed consumers are t01A08,
t01J04, t92J07, and t96J05. Implicit-function kernel parametrizations still
need instantiation, and applicable jet-locus images must be transferred
into this exact flat parameter locus. Jet cases outside the strict
dimension range remain unresolved before rectangular induction. No
automatic remaining-order admissibility or frozen consumer closure is claimed.

The source is byte-identical to the accepted fixture
`/tmp/SardC1ParameterizedFlatLocusNullityProbe.lean`, SHA-256
`e338a616dfe4649b9586bffc44ca6f83daa890feab49c39752d4905844e0910b`.
The declaration uses only propext, Classical.choice, and Quot.sound.
The stop boundary is failure of ambient closedness or the relative
closed-open preimage representation under the stated continuity
hypotheses, or a need for nonstandard axioms.

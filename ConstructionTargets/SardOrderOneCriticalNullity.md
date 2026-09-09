# Admissible order-one critical nullity

`orderOne_criticalImage_zero` proves nullity of the localized nonsurjective
ambient derivative image for finite-dimensional real normed spaces, a Borel
target with additive Haar measure, and pointwise ambient C1 regularity on an
arbitrary source set. It assumes `SardOrderAdmissible` at order one.

Unfolding admissibility gives source finrank at most target finrank. C1
regularity supplies ambient differentiability. For strictly smaller source
dimension, `lowerDimension_ambient_image_zero` makes the entire image null,
so its critical image is null by containment. For equal dimensions,
`equalDimension_ambient_criticalImage_zero` supplies the conclusion directly.
These are the observed theorem dependencies; the admissibility module also
supplies the definition used in the statement.

There is no induction hypothesis, supplied coordinate model, source measure,
or source measurable structure. No openness or measurability of the source
set is required. This theorem is specifically order one: it does not assert
an order-zero result or settle complementary higher-order analytic cases.

The Lean source matches `/tmp/SardOrderOneCriticalNullityProbe.lean`, SHA-256
`e200f66aaf9163af4b74ae794f07c3b06c15aef313c5d902e2ff155441c93b45`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Intended consumers are t93A04 and the shared Sard foundations for t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is closed here. The next edge
is integration into the induction interface; its order-zero obligation and
complementary higher-order analytic cases remain before rectangular closure.
The ledger and frozen consumer are unchanged.

The mathematical boundary would be failure of the dimension implication,
the C1 differentiability implication, either reviewed dimensional nullity
result under the stated hypotheses, or a need for nonstandard axioms.

# First nonzero jet local kernel Taylor nullity

Provides `exists_open_firstNonzeroJet_image_null_of_kernel_taylor_surplus`.
The Lean module is byte-identical to the accepted probe fixture (SHA-256
`b3cc06b85c2d982493915dfb2327769b28dbb804bb4c9f23c413bef786b5d2c9`).

## Statement and construction

For a scalarized i-jet implicit-function chart based at a first-nonzero-(i+1)-jet
point, assume i >= 1, global C^(i+1) ambient regularity, C1 regularity of the
exact inverse kernel parametrization at the base coordinate, and the strict
bound kernelDim < (i+1)*targetDim. The finite-dimensional inner-product,
nontrivial, Borel, and proper-space assumptions are retained as stated in Lean.
The conclusion is an open source neighborhood containing the base point whose
localized jet image has zero measure for the specified target add-Haar measure.

Base-point regularity supplies an open parameter neighborhood V. Intersecting
V with the chart target slice gives pointwise C1 regularity there. The exact
restricted-kernel image identity supplies a compatible open source neighborhood
W. Vanishing scalarized i-jets places each localized jet point in the required
level set. Its parameter witness preserves ambient derivatives of orders 1
through i, so exact flat-parameter locus nullity and measure monotonicity give
the conclusion. No lower-dimensional Sard nullity hypothesis is assumed.

## Dependencies and consumer boundary

Uses the reviewed local kernel regularity, restricted parameterization,
scalarized jet level containment, and C1 flat-parameter locus nullity results.
The full-target-slice kernel Taylor module is imported, but its stronger
whole-slice regularity hypothesis is not required by this construction.

Intended consumer: t93A04. Other proposed consumers: t01A08, t01J04, t92J07,
t96J05. No frozen consumer is changed or closed by this infrastructure packet.
The next step is to supply base-point kernel C1 regularity from scalarized jet
chart data and aggregate local witnesses. Jet cases outside the strict Taylor
dimension range still require analytic repair before rectangular induction.
This result does not establish rectangular Morse-Sard.

## Verification

Compile the module and accepted fixture, compare their bytes, build the focused
module, and inspect the included axiom report. Expected axioms are only
`propext`, `Classical.choice`, and `Quot.sound`; no warnings are expected.
The stop boundary is failure of the stated C1 localization or restricted-image
transfer, or a requirement for nonstandard axioms.

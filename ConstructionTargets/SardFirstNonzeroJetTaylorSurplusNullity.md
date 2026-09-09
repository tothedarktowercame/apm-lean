# First nonzero jet Taylor-surplus nullity

Provides `firstNonzeroJetLocus_image_null_of_taylor_surplus`.
The module is byte-identical to the accepted fixture with SHA-256
`010bdca420d4465e0049ab2bdc06f7ecc9c313cdd7e93bcdd94d22493b2f53b6`.

## Statement

For a globally C^(i+1) map between finite-dimensional real inner-product spaces,
assume i >= 1, sourceDim > 1, and sourceDim-1 < (i+1)*targetDim. The target is
nontrivial and carries its Borel measurable structure and an add-Haar measure.
The image of the entire first-nonzero-(i+1)-jet locus in an arbitrary source
subset K has zero target measure. No chart data, criticality assumption on K,
or lower-dimensional Sard nullity hypothesis is supplied by the caller.

## Proof and dependencies

At each locus point the reviewed scalarized-chart construction selects scalar
directions and an implicit-function chart. Its remaining order is set to one;
global C^(i+1) regularity therefore supplies base-point C1 kernel regularity.
The scalar derivative kernel has dimension sourceDim-1 by the reviewed exact
codimension-one identity. The source dimension hypothesis makes this kernel
nontrivial. Its Borel structure and second-countability instance are passed
explicitly to the local kernel Taylor nullity theorem. Strict surplus gives
an open null-image neighborhood. The reviewed second-countable jet-locus
aggregation theorem then gives nullity of the whole locus image.

Observed dependencies are local kernel Taylor nullity, scalarized chart data,
scalar derivative kernel dimension, and jet-locus local aggregation. Expected
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

## Consumer boundary

Intended consumer: t93A04. Other proposed consumers: t01A08, t01J04, t92J07,
t96J05. No frozen consumer is changed or closed by this infrastructure packet.
Apply the theorem to orders satisfying strict Taylor surplus. Source dimensions
at most one and jet orders outside that range still require separate arguments
before rectangular induction and exhaustion. This is not full Morse-Sard.

Stop only if the stated chart construction, codimension-one identity, or local
aggregation fails to imply this nullity, or nonstandard axioms are required.
Verification consists of fixture comparison, direct compilation of both files,
a focused module build, axiom inspection, and frozen-consumer checks.

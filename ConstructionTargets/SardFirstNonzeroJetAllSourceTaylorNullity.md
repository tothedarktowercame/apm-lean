# All-source first nonzero jet Taylor nullity

Provides `firstNonzeroJetLocus_image_null_of_taylor_surplus_all_source_dimensions`.
The module is byte-identical to the accepted fixture, SHA-256
`c53a45fa2ef38247079c3633bf9417cede8c78a50b2dab6a5ee4f69dcafe41d9`.

## Statement and proof

For finite-dimensional real inner-product source and target spaces, global
C^(i+1) regularity, i >= 1, and sourceDim-1 < (i+1)*targetDim imply nullity of
the entire first-nonzero-(i+1)-jet locus image in an arbitrary source set K.
The source is complete. The target is nontrivial with its Borel measurable
structure and the specified add-Haar measure. Natural subtraction is used
in the dimension bound. No lower bound on source dimension is required.

When sourceDim > 1, the reviewed Taylor-surplus theorem applies. Otherwise,
at each jet-locus point, scalarized chart data and the exact codimension-one
identity show that the derivative kernel has dimension zero. Its subsingleton
instance makes any two inverse-kernel parameter witnesses equal. Reviewed
chart containment therefore makes the localized jet locus subsingleton.
Its image is null because the target add-Haar measure has no atoms. The
reviewed local-to-global aggregation theorem completes the argument.

The proof consumes Taylor-surplus nullity, scalarized chart data, scalar
derivative kernel dimension, kernel parameter containment, and jet-locus
local aggregation. Expected axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Consumer boundary and verification

Intended consumer: t93A04. Other proposed consumers: t01A08, t01J04, t92J07,
t96J05. No frozen consumer is changed or closed by this infrastructure packet.
The low-source-dimension boundary is discharged. Jet orders outside strict
surplus still require analytic repair before rectangular induction and
exhaustion; this is not full rectangular Morse-Sard.

Verify fixture identity, direct compilation, focused build, axiom report,
worklist validity, and unchanged frozen consumer. Stop only if the stated
codimension-one/subsingleton argument or null-image transfer fails, or
nonstandard axioms are required.

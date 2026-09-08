# Finite-order pointwise witness explicit measurable spaces

This construction fixes the measurable-space parameters used by the derivative-range and orthogonal-residual Borel proofs to their inherited subtype instances.  It is the elaboration boundary needed before specializing the generic finite-order pointwise rank-chart nullity witness with coordinate measures carrying those same measurable spaces.

The theorem `projectedCoordinates_explicit_measurableSpace_borel_bindings` records both bindings together.  The wrapper `exists_open_rankLocus_image_zero_explicit_measurableSpaces` then takes the two measurable spaces as ordinary explicit arguments, followed by Borel proofs, coordinate measures, and additive-Haar proofs indexed by those exact spaces.  Only after installing them does it invoke the generic pointwise nullity witness.  Both declarations use only the standard axioms reported by Lean.

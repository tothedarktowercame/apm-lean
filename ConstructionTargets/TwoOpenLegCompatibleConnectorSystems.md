# Two-open leg-compatible connector systems

This target constructs connector systems on the fundamental groupoids of an
overlap and its two open-cover pieces.  The piece connector at a point of the
overlap is defined to be the image of the overlap connector, so both required
`mapIso` compatibility equations hold exactly.

Path connectedness supplies connectors within each piece.  Simple
connectedness supplies both an overlap point and the overlap paths.  The
result is packaged by `existsTwoOpenLegCompatibleConnectorSystems` for use by
the generic connector-to-single-object comparison.

This file does not perform the simply-connected vertex-group reduction, build
the point-span/free-product mapping equivalence, reconstruct a source
equivalence, or specialize to either consumer.

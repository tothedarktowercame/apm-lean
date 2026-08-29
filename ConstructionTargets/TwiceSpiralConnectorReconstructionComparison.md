# Connector reconstruction comparison

This target compares an arbitrary coordinate pseudococone `Q` with the result
of extracting its two vertex-group actions and reconstructing them using fixed
leg-compatible connectors.

`leftReconstructionIso` and `rightReconstructionIso` have components
`Q.left.mapIso (K.left.connector X)` and
`Q.right.mapIso (K.right.connector X)`.  In particular, the connector at its
own base is retained and is not assumed to be the identity.  Naturality is the
image under `Q.left` or `Q.right` of the connector normal-form reconstruction
identity.

`reconstruction_glue_square` rewrites the two piece connectors with
`left_connector_map` and `right_connector_map`, then applies the naturality of
`Q.glue.hom` at the chosen boundary connector.  The inverse square is derived
by categorical cancellation.

`reconstructionHom`, `reconstructionInv`, and `reconstructionIso` package an
isomorphism from reconstruction-after-extraction to `Q`.  Naturality of this
objectwise isomorphism in pseudococone morphisms remains the next categorical
packet; no equivalence of categories is claimed here.

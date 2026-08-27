# Product evenly-covered trivialization

`isEvenlyCovered_productMap` pairs two explicit `IsEvenlyCovered`
trivializations.  Over neighborhoods `U` and `V`, it constructs the product
neighborhood `U ×ˢ V`, identifies its preimage with the product of the two
preimages, and rearranges the two local homeomorphisms into a homeomorphism
with fiber `I × J`.

The theorem is local and generic.  It assumes only the two input
`IsEvenlyCovered` witnesses; it does not assume a product covering theorem,
deck-group structure, fiber transitivity, or any conclusion of frozen
`t01A02`.

`productFiberHomeomorph` explicitly identifies the product of the coordinate
fibers with the fiber of `productMap`.  Using that identification,
`isCoveringMap_productMap` derives the generic product-covering result from the
local construction.

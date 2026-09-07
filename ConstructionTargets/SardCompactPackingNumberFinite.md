# Compact sets have finite packing number at nonzero radius

`IsCompact.packingNumber_ne_top` proves that a compact subset of a proper
metric space has a non-infinite `ENat`-valued packing number at every nonzero
`NNReal` separation radius.  It obtains a finite half-radius external cover and
uses Mathlib's packing-versus-external-covering inequality.

This theorem supplies the finiteness hypothesis needed by the maximal separated
set API.  It does not extract that set, prove its maximality cover, or obtain the
quantitative polynomial cardinality and Taylor-volume exponent estimates.  The
remaining Sard obligation is one maximal-separated-set extraction and
finite-dimensional packing/Taylor exponent estimate, before local rank
reduction.

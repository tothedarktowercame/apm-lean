# Maximal separated covers represented as finsets

`exists_finset_maximal_separated_cover` converts Mathlib's set-valued maximal
separated construction into the `Finset` representation used by finite packing
and measure sums.  Assuming the `ε`-packing number is not top, it returns a
finite family of centers contained in the source set that is both
`ε`-separated and an `ε`-cover.

This adapter does not establish packing-number finiteness or derive the
polynomial cardinality estimate from ball volumes.  It also does not apply the
Taylor target-ball bound.  The remaining Sard obligation is one
finite-dimensional polynomial packing bound and Taylor target-volume exponent
estimate, before local rank reduction.

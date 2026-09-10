# Balanced Boolean product-simplex words

`ConstructionTargets.ProductSimplexBalancedWords` packages the exact
balanced-word representation consumed by later maximal-path reconstruction.

A `BalancedWord p q` contains a Boolean function on exactly `Fin (p+q)`. Its
`horizontal_total` and `vertical_total` fields state, using the exported
terminal `horizontalCount` and `verticalCount`, that the full word contains
`p` true letters and `q` false letters. The coercion exposes the stored word as
a function. `terminal_partition` rewrites by those two fields to show that the
totals partition the full length `p+q`.

This module proves no prefix monotonicity and constructs no cumulative path,
inverse law, corner swap, face pairing or cancellation, chain sum, cross
product, Eilenberg-Zilber, Kunneth, intersection, or consumer result. The next
step exposes prefix-count monotonicity, bounds cumulative coordinates by the
balanced totals, constructs the canonical path, and proves the word/path
inverse laws.

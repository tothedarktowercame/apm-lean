# Prefix counts for Boolean product-simplex words

`ConstructionTargets.ProductSimplexWordPrefixCounts` provides the finite
prefix arithmetic needed to reconstruct a path from a balanced Boolean word.

For a word `w : Fin n → Bool` and endpoint `i : Fin (n+1)`, the private prefix
is the set of existing indices `k` with `k.val < i.val`. `horizontalCount`
counts its true letters and `verticalCount` counts its false letters.
`horizontalCount_add_verticalCount` proves that these complementary filters
partition the prefix and that their cardinalities sum to `i`. The remaining
two theorems derive the bound of each count by `i`.

`horizontalCount_mono` and `verticalCount_mono` prove monotonicity for ordered
prefix endpoints. The subset argument lives in this module so it can use the
private `wordPrefix` representation without exposing that implementation.

No balanced-word subtype or terminal balance assumption appears here. The
module does not reconstruct paths, prove inverse laws, define corner swaps,
pair or cancel faces, construct chain sums or a cross product, or assert
Eilenberg-Zilber, Kunneth, intersection, or consumer results. The next step
uses the resulting balanced total bounds as cumulative path coordinates.

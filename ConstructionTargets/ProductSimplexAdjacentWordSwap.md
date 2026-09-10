# Generic adjacent Boolean-word transposition

`ConstructionTargets.ProductSimplexAdjacentWordSwap` defines the adjacent
transposition of an arbitrary word `Fin (n+1) → Bool` at a cut `i : Fin n`.
The operation precomposes the word with
`Equiv.swap i.castSucc i.succ`.

`adjacentSwapWord_left` and `adjacentSwapWord_right` state that the two adjacent
positions exchange values. `adjacentSwapWord_of_ne` states that every position
distinct from both remains unchanged. `adjacentSwapWord_involutive` proves
functionally that applying the same transposition twice returns the original
word.

No unequal-letter or balance assumption is used. The module does not package a
balanced-word or maximal-path swap, compare deleted faces, assign shuffle
signs, cancel chains, construct a cross product, or assert Eilenberg-Zilber,
Kunneth, intersection, or consumer results.

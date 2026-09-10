# Boolean step words of maximal product-simplex paths

`ConstructionTargets.ProductSimplexStepWord` converts each canonical maximal
product-simplex path into a Boolean word with exact local coordinate semantics.

`stepWord z i` is `true` precisely when the canonical
`ProductSimplexShuffleParity.IsHorizontal z i` predicate holds. The true and
false equivalence theorems expose both directions of this definition.
`stepWord_true_coordinates` proves that a true letter increases the first
coordinate by one and fixes the second; `stepWord_false_coordinates` proves
that a false letter fixes the first coordinate and increases the second by
one. Both conclusions use natural-number coordinates and follow from the
banked unit-step dichotomy.

This module does not reconstruct a path from a word, swap corners, pair faces,
prove a sign change or cancellation, define chain sums or a cross product, or
assert Eilenberg-Zilber, Kunneth, intersection, or consumer results. The next
step defines bounded words with exactly `p` true and `q` false letters,
reconstructs their cumulative-coordinate paths, proves the inverse laws, and
implements the adjacent unlike-letter swap.

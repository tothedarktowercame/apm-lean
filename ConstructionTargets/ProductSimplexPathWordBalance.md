# Balanced step words of maximal product-simplex paths

`ConstructionTargets.ProductSimplexPathWordBalance` records how the Boolean
step word of an arbitrary canonical maximal path counts its grid coordinates.
At every prefix endpoint, `horizontalCount_stepWord` identifies the horizontal
count with the first coordinate, and `verticalCount_stepWord` identifies the
vertical count with the second coordinate.

The horizontal identity is proved by `Fin` induction. Its base case combines
the prefix partition at zero with `grid_start`; each successor case uses the
true or false count recurrence and the corresponding exact step-coordinate
theorem. The vertical identity follows from the prefix partition and the
maximal-path coordinate sum.

At the terminal endpoint, `grid_end` turns these coordinate identities into
totals `p` and `q`. Thus `balancedStepWord` packages exactly `stepWord z` as a
`BalancedWord p q`, with `balancedStepWord_toWord` exposing that definitional
equality.

The module does not prove reconstruction after extraction, package an
equivalence, define corner swaps, cancel faces, construct chain sums or a cross
product, or assert Eilenberg-Zilber, Kunneth, intersection, or consumer results.

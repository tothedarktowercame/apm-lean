# Adjacent maximal-path swaps

`ConstructionTargets.ProductSimplexAdjacentPathSwap` transports the balanced
adjacent-word swap to canonical `MaximalPath p q` values.  The definition
conjugates `balancedAdjacentSwap` through `wordPathEquiv p q`, using the same
length witness `n + 1 = p + q` and cut `i : Fin n`.

`adjacentSwapPath_word` identifies the inverse image of the transported path
with the balanced swapped word.  `adjacentSwapPath_toWord` gives its underlying
Boolean-word coordinate equation, and `adjacentSwapPath_involutive` proves
that applying the transported swap twice returns the original maximal path.

The module does not compare faces, assume unequal adjacent letters, assign
signs, cancel chains, construct a cross product, edit consumer sources, or
state consumer closure.

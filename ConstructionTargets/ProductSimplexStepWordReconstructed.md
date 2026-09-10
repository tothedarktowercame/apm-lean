# Step word of a reconstructed product-simplex path

`ConstructionTargets.ProductSimplexStepWordReconstructed` proves the forward
inverse law for the cumulative-count reconstruction of a balanced Boolean word.
For every `BalancedWord p q`, reading `stepWord` from `reconstructedPath`
returns its original Boolean word pointwise.

At a true letter, the horizontal prefix count successor theorem gives the
required first-coordinate increment. At a false letter, the corresponding
horizontal count stays fixed, contradicting the increment that a horizontal
step would require. The proof interprets these coordinate facts through the
canonical `IsHorizontal` characterization of `stepWord`.

The module does not extract a balanced word from an arbitrary path, prove the
reverse inverse law, package an equivalence, define corner swaps, cancel faces,
construct chain sums or a cross product, or assert Eilenberg-Zilber, Kunneth,
intersection, or consumer results.

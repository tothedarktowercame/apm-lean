# Quantitative Taylor cover measure

`exists_taylor_cover_measure_lt` constructs, at a geometric radius, a finite
separated cover of a compact bounded subset of a finite-dimensional real
inner-product space. A uniform order-`k + 1` remainder estimate maps every
source patch into its Taylor target ball, and the positive Morse--Sard exponent
equation makes the total image volume smaller than any positive `ENNReal`
tolerance.

The theorem composes the promoted maximal-separated cover cardinality, finite
Taylor target-cover measure, exponent normalization, and NNReal geometric-scale
tolerance results. It preserves the fixture's compactness, separation,
remainder, exponent, and measure conclusions and uses only standard axioms.

The remaining consumer work is to derive the uniform multivariable
order-`k + 1` remainder inequality from sufficient `ContDiff` regularity and
vanishing iterated derivatives on the bounded locus, then apply this theorem
before local rank reduction.

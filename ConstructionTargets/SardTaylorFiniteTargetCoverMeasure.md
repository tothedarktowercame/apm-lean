# Taylor finite target-cover measure

`finiteCover_taylor_image_measure_le_card_mul_ballVolume` converts a finite
NNReal-radius source cover and a uniform order-`k + 1` Taylor remainder bound
at its centres into two conclusions: the source image is covered by finitely
many closed target balls, and its volume is at most the number of centres times
the exact finite-dimensional volume of one such ball.

The theorem composes the promoted source-cover, Taylor ball-image, finite-union
measure, uniform finite-sum, and finite-dimensional ball-volume interfaces. It
uses only standard axioms.

The remaining consumer work is to combine this target-volume estimate with the
explicit maximal-separated cover cardinality bound, normalize real and ENNReal
powers, cancel the source dimension against the Taylor exponent, and choose a
scale using positive-power tolerance.

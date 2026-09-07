# ENNReal enlarged half-radius ratio

`ENNReal.enlarged_halfRadius_ratio` rewrites the quotient of the enlarged
radius `R + ρ / 2` by the half-radius `ρ / 2` into the single coercion
`ENNReal.ofReal ((2 * R + ρ) / ρ)`. The sole hypothesis `0 < ρ` supplies the
positive denominator required by `ENNReal.ofReal_div_of_pos`.

The declaration promotes the compiled fixture without changing its positivity
hypothesis or representation. The remaining consumer work is one polynomial
source-cover bound and Taylor target-volume exponent estimate before local rank
reduction.

# Arbitrarily small measure bounds imply nullity

`measure_eq_zero_of_le_inv_nat` converts inverse-natural upper bounds on the
measure of one fixed set into exact nullity.  If `μ s ≤ (n : ENNReal)⁻¹` for
every natural number `n`, positivity of `μ s` would contradict
`ENNReal.exists_inv_nat_lt`.

This theorem supplies only the limiting order argument.  It does not construct
the finite covers or derive their inverse-natural bounds from smooth flatness.
The remaining Sard obligation is one smooth flat-locus scale-cover construction
and inverse-natural estimate theorem, before local rank reduction.

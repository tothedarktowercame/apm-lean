# Multivariable Taylor covering nullity

This module promotes the complete compiled covering-nullity interface.

For a compact bounded flat locus, `exists_smooth_flat_taylor_cover_measure_lt` first derives one uniform order-`k + 1` Taylor remainder constant, then invokes the quantitative separated-cover construction at every positive target-volume tolerance. The result includes the finite centres, source cover, target-ball cover, and strict volume estimate.

`smooth_flat_locus_image_volume_eq_zero` applies these estimates at every inverse-natural tolerance and uses `measure_eq_zero_of_le_inv_nat` to conclude exact nullity.

The remaining consumer work is local rank reduction and rank/source-dimension induction for the rectangular Morse--Sard theorem.

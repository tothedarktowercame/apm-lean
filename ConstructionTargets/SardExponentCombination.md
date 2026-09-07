# Cover-target exponent combination

`ENNReal.mul_bounds_cancel_dimension` combines the inverse source-cover bound
`card ≤ A * r⁻¹ ^ m` with the target-ball bound
`per ≤ B * r ^ (m + d)`. For a nonzero finite ENNReal radius, multiplication
cancels the `m` powers and leaves `card * per ≤ A * B * r ^ d`.

The theorem promotes the compiled fixture without changing its hypotheses or
representation. The remaining consumer work is one polynomial source-cover
theorem and positive-power tolerance choice before local rank reduction.

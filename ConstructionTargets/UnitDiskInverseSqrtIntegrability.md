# Unit-disk inverse-square-root integrability

This target proves the analytic estimate isolated by
`HemisphereInverseSqrtDiskIntegral`: the kernel

`1 / sqrt (1 - x^2 - y^2)`

is integrable on the closed unit disk (indeed, its totalized zero extension is
integrable on the whole plane).  The proof uses the additive-Haar radial
integrability criterion.  Its one-dimensional density is reduced by the
monotone substitution `u = 1 - r^2` to `u^(-1/2)`, whose endpoint singularity
is covered by Mathlib's `intervalIntegrable_rpow'` theorem.  Beyond radius one
the total inverse is zero, including on the boundary circle.

The coordinate-odd integrals are not stated here: their cancellation is a
separate measure-preserving reflection calculation, while this file supplies
the previously missing integrability premise without assuming a disk-integral
value, Stokes' theorem, or the frozen problem conclusion.

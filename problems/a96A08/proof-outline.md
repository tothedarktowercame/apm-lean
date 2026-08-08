# Proof Outline: a96A08

The analytic evaluation is formalized through the symmetric truncation limit.
The absolute-integrability bridge is now closed, so the final theorem follows
from `apm_a96A08_integrable`, `tendsto_symmetric_f`, and Mathlib's
`intervalIntegral_tendsto_integral`. The complete file is sorry-free.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a96A08.md`

## Absolute integrability

On the compact middle interval, integrability follows a.e. from the proved
partial-fraction identity and interval integrability of the two removable sinc
terms. On `|x| ≥ 2`, the proof uses

`|sin(πx)/(x²-x)| ≤ 2/x²`

and `integrableOn_Ioi_rpow_of_lt` for the power `x⁻²`. The negative tail is
obtained by `comp_neg_Iio`; the two tails and `Icc (-2) 2` are united and their
union is shown to equal `univ`.

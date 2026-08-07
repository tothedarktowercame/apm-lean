# Proof Outline: a96A08

The analytic evaluation is formalized through the symmetric truncation limit.
The final theorem now follows from `a96A08_integrable`,
`tendsto_symmetric_f`, and Mathlib's `intervalIntegral_tendsto_integral`.
Several inference and congruence-direction errors in the imported intermediate
proofs were also repaired, so the complete file validates again.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a96A08.md`

## Remaining bridge

Only absolute integrability remains.  On the compact middle interval it
follows a.e. from the proved partial-fraction identity and interval
integrability of the two removable sinc terms.  On `|x| ≥ 2`, use

`|sin(πx)/(x²-x)| ≤ 2/x²`

and the existing integrability theorem for the power `x⁻²` on a half-line.
The remaining formal work is splitting the domain, proving the two elementary
denominator bounds, reflecting the negative tail, and recombining the three
restricted integrability results.

# Proof Outline: m94J03

The Lean artifact reduces the theorem to one continuous-functional-calculus
identity. Spectral distance positivity and the full scalar inverse estimate are
compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94J03.md`

## Formalized

- The subsingleton Hilbert-space case.
- Resolvent membership implies exclusion from the spectrum.
- Closed nonempty spectrum gives strictly positive spectral distance.
- For every spectral value `lam`,
  `‖(z-lam)⁻¹‖ ≤ infDist(z, spectrum A)⁻¹`.

## Remaining Boundary

Identify `resolvent A z` with the continuous functional calculus of
`lam ↦ (z-lam)⁻¹`, using `cfc_inv`/`cfc_ringInverse_id`, then apply
`norm_cfc_le` to the compiled pointwise estimate. Compactness is not needed
after self-adjointness supplies the normal CFC instance.

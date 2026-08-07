# Proof Outline: m94J03

The Lean artifact proves the resolvent estimate through the isometric
continuous functional calculus. Spectral distance positivity, the scalar
inverse estimate, and the resolvent/CFC identity are all compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94J03.md`

## Formalized

- The subsingleton Hilbert-space case.
- Resolvent membership implies exclusion from the spectrum.
- Closed nonempty spectrum gives strictly positive spectral distance.
- For every spectral value `lam`,
  `‖(z-lam)⁻¹‖ ≤ infDist(z, spectrum A)⁻¹`.
- `cfc_inv`, `cfc_sub`, `cfc_const`, and `cfc_id'` identify `resolvent A z`
  with the CFC of `lam ↦ (z-lam)⁻¹`; `norm_cfc_le` then proves the result.

## Remaining Boundary

None. Compactness is not needed after self-adjointness supplies the normal CFC
instance.

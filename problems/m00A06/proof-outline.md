# Proof Outline: m00A06

The Lean artifact is partial. It now completes the divided-difference proof of
integrability when the test function vanishes at zero.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m00A06.md`

## Compiled Helpers

- `dslope φ 0` is continuous whenever `φ` is differentiable.
- Away from zero, the singular integrand equals `dslope φ 0` multiplied by
  the bounded sign factor `|x|⁻¹x` when `φ 0 = 0`.
- The divided difference has compact support; multiplication by the measurable
  sign factor preserves integrability, and a.e. equality transfers this to the
  original singular integrand.
- A `ContDiffBump` with inner radius one is a compactly supported test function
  equal to one on `[0,1]`. Restricting hypothetical integrability of its
  singular product to this interval contradicts `intervalIntegrable_inv_iff`.

## Remaining Boundaries

- Assemble the finite-part linear functional and its uniform order-one
  seminorm estimate on each compact support. This is now stated precisely as
  `apm_m00A06_bridge_finitePart`.
- Recombine its two defining set integrals with the ordinary singular integral
  when `φ 0 = 0`. This is stated as
  `apm_m00A06_bridge_finitePart_eq_integral`.

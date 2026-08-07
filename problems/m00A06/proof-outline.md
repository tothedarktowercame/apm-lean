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

## Remaining Boundaries

- Construct a bump plateau and reduce its product to nonintegrability of
  `|x|⁻¹` near zero.
- Assemble the finite-part linear functional and its uniform order-one
  seminorm estimate on each compact support.

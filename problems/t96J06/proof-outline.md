# Proof Outline: t96J06

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t96J06.md`

## Compiled progress

- Construct the projective point represented by the first coordinate vector.
- Use `Submodule.mk_mem_projectivization_iff` to prove it lies in the coordinate
  projective line.
- Pair the point with itself to prove `ℝP¹ × ℝP¹` is nonempty.
- Construct the third-coordinate projective point outside `ℝP¹` and prove the
  embedded product is a proper subset of the ambient product.
- `apm_t96j06_mk_pair_mem_ProductSubspace_iff` characterizes arbitrary
  projective representatives in the product by the equations `u 2 = 0` and
  `v 2 = 0`, making the codimension-two incidence condition explicit.

## Remaining obstruction

The intended contradiction requires a mod-two intersection theory:

1. Construct the ambient mod-two class of `ℝP¹ × ℝP¹`.
2. Show an embedded intrinsic boundary represents zero in ambient homology.
3. Compute the class's self-intersection as one, using the projective-line
   intersection in each factor and a Künneth/product formula.

Mathlib currently lacks the required projective-space homology, Künneth,
intersection pairing, and completed bordism infrastructure.

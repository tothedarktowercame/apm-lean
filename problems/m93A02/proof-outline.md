# Proof Outline: m93A02

The Lean artifact proves the nonsurjective counterexample and now constructs
the algebraic inverse required by the contraction argument, including its sharp
norm bound. One fixed-point assembly boundary remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93A02.md`

## Formalized

- The lower bound makes `L` injective; with surjectivity this gives a
  `LinearEquiv H K`.
- Its inverse satisfies `‖L⁻¹ k‖ ≤ δ⁻¹ ‖k‖`.
- The explicit parabola counterexample proves failure without surjectivity.

## Remaining Boundary

Define `h ↦ L⁻¹(k - Q h h)`, prove it maps the chosen closed ball into
itself and is contracting, handle `M = 0` separately, and apply
`ContractingWith.exists_fixedPoint'` to the complete closed ball subtype.

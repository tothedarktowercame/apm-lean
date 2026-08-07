# Proof Outline: m01J02

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m01J02.md`

## Closer hop 1 progress

- The canonical projection facts for `M.starProjection` are complete.
- The product criterion is complete: self-adjointness of the product gives
  commutation through `ContinuousLinearMap.adjoint_comp`; commutation gives
  idempotence and self-adjointness.
- Under commutation, the product range is proved equal to `M ⊓ N`.
- One sorry remains in the sum criterion. The missing direction expands the
  idempotence of `P_M + P_N` to vanishing symmetric cross terms and then needs
  the positivity/inner-product argument proving either cross composition is
  zero. No packaged Mathlib converse to `IsStarProjection.add` was found.

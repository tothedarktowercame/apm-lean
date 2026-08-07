# Proof Outline: m01J02

The canonical Lean attempt is `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m01J02.md`

## Formal proof

- The canonical projection facts for `M.starProjection` are complete.
- The product criterion is complete: self-adjointness of the product gives
  commutation through `ContinuousLinearMap.adjoint_comp`; commutation gives
  idempotence and self-adjointness.
- Under commutation, the product range is proved equal to `M ⊓ N`.
- The sum criterion is complete. Applying the sum equality to vectors already
  in either summand forces the cross projection to vanish, avoiding the longer
  positivity argument. Conversely, the sum has range in `M ⊔ N` and its
  residual is orthogonal to both summands, so projection uniqueness applies.

There are no remaining proof obligations.

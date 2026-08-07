# Proof Outline: b93A04

The Lean proof is complete.

- The finite-sum description is obtained from the range of
  `Algebra.TensorProduct.productMap`; `TensorProduct.exists_sum_tmul_eq`
  converts an arbitrary preimage into the required `Fin n` sum.
- Galoisness of the compositum follows from the existing instances.
- Both fixing-subgroup identities follow from `fixingSubgroup_sup` and the
  order-dual Galois correspondence.
- When the compositum is top, the product of the two restriction maps is
  injective because its kernel is the fixing subgroup of top. Commutativity
  of both target Galois groups therefore pulls back to `Gal(K/F)`.

## Verification

`lake env lean problems/b93A04/lean/Main.lean` succeeds with no sorries.

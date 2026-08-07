# Proof Outline: b98J02

The Lean proof is complete.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b98J02.md`

## Formal route

1. Apply `Ideal.subset_union_prime` for finite prime avoidance.
2. Restrict `Gal(M/L)` to the abstract integral-closure model `B` using
   `galRestrict`, obtaining a `MulSemiringAction` that fixes `A`.
3. Use `hinter` and the Galois fixed-field theorem to prove
   `Algebra.IsInvariant A B Gal(M/L)`.
4. The product of the Galois translates of `x` is invariant, hence comes from
   `A`; its identity factor puts it in `P`, and mapping it into `M` gives the
   product required by the statement.
5. Apply `Algebra.IsInvariant.exists_smul_of_under_eq` to the two primes and
   translate pointwise ideal action through `galRestrict` to obtain the stated
   elementwise formulation.

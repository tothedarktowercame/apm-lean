# Proof Outline: b93A03

The Lean proof is complete in `lean/Main.lean`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b93A03.md`

## Formal proof

- Tensor products preserve surjections, while multiplication by `n` supplies
  the non-injectivity witness after tensoring with `ZMod n`.
- A local naturality argument proves that the custom flatness predicate is
  invariant under additive equivalence.
- Infinite cyclic groups are classified by `intCyclicAddEquiv`; finite cyclic
  groups by `zmodAddCyclicAddEquiv`. Finite cardinality one is the subsingleton
  case, while cardinality at least two is ruled out by the `ZMod n` witness.

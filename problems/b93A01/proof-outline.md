# Proof Outline: b93A01

The Lean proof has closed the order-`pq` structural conclusions:

- Sylow counting constructs the unique normal subgroup of order `q`.
- If a normal subgroup of order `p` also exists, the two subgroups are
  complementary, cyclic, and commute, so `G` is abelian.
- Cardinal divisibility already excludes an embedding in `S_(q-1)`.

## Remaining boundary

One sorry remains around the faithful-permutation assertions. The nonabelian
branch needs the faithful coset action on a `q`-element quotient, including
the normal-core kernel argument and transport to `Fin q`. The abelian branch
needs explicit disjoint prime cycles and the sharp cycle-support lower bound
in degree `p + q - 1`.

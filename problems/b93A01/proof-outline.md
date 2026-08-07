# Proof Outline: b93A01

The Lean proof has closed the order-`pq` structural conclusions:

- Sylow counting constructs the unique normal subgroup of order `q`.
- If a normal subgroup of order `p` also exists, the two subgroups are
  complementary, cyclic, and commute, so `G` is abelian.
- Cardinal divisibility already excludes an embedding in `S_(q-1)`.
- `apm_b93a01_embeds_fin_of_faithful_action` transports any faithful action
  on an abstract finite `n`-element type to an embedding in permutations of
  `Fin n`.

## Remaining boundary

One sorry remains around the faithful-permutation assertions. The nonabelian
branch needs the faithful coset action on a `q`-element quotient. Transport to
`Fin q` is now solved; the remaining step is the normal-core kernel argument,
likely via `Subgroup.eq_bot_or_eq_top_of_prime_card`. The abelian branch
needs explicit disjoint prime cycles and the sharp cycle-support lower bound
in degree `p + q - 1`.

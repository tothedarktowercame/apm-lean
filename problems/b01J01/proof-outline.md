# Proof Outline: b01J01

The frozen theorem is partially proved in `lean/Main.lean`.

Closer hop 1 fully proves part (a) in
`apm_b01j01_prime_dvd_quotient`. The proof identifies
`K.relIndex H` with `[H : H ⊓ K]`, applies Lagrange's cardinality
identity, uses primality to deduce `p ∣ K.relIndex H`, and finishes with
`Subgroup.relIndex_dvd_index_of_normal`.

Closer hop 3 adds `apm_b01j01_prime_dvd_abelianization`, specializing part
(a) to `commutator G`. This proves the full numerical reduction for part (b):
the prime divides the cardinality of the finite abelianization.

The remaining boundary consists of:

1. extracting an order-`p` quotient of the finite abelianization and pulling
   its kernel back to an index-`p` subgroup for part (b);
2. proving the normal-subgroup restriction theorem that `P ⊓ K` is Sylow
   in `K` for ambient Sylow `P`, completing part (c);
3. proving the newly stated `apm_b01J01_bridge_trace_constant_fiber`, which
   says every trace fiber has one cardinal `c` and gives the exact product
   formula `Nat.card (Sylow p G) = Nat.card (Sylow p K) * c`.

Mathlib's `Sylow.exists_comap_subtype_eq` already gives the reverse
existence direction needed in part (c).  Closer hop 2 packages it as
`apm_b01j01_sylowSubgroupsIn_subset_traces`, including the exact map/comap
rewrite required by the frozen set encoding.  Mathlib does not package the
other inclusion or the cardinal-divisibility theorem.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01J01.md`

## Follow-up Needed

- extract an index-`p` subgroup of the finite abelian quotient for part (b)
- transport Sylow maximality through conjugation and normality of `K` for the
  reverse inclusion in part (c)
- prove `apm_b01J01_bridge_trace_constant_fiber`; divisibility in part (d)
  then follows immediately from its product formula

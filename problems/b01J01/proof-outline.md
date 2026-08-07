# Proof Outline: b01J01

The frozen theorem is partially proved in `lean/Main.lean`.

Closer hop 1 fully proves part (a) in
`apm_b01j01_prime_dvd_quotient`. The proof identifies
`K.relIndex H` with `[H : H ⊓ K]`, applies Lagrange's cardinality
identity, uses primality to deduce `p ∣ K.relIndex H`, and finishes with
`Subgroup.relIndex_dvd_index_of_normal`.

The remaining boundary consists of:

1. extracting an index-`p` subgroup from the relevant finite abelian
   quotient for part (b);
2. proving the normal-subgroup restriction theorem that `P ⊓ K` is Sylow
   in `K` for ambient Sylow `P`, completing part (c);
3. formalizing the constant-fiber/orbit count giving the divisibility in
   part (d).

Mathlib's `Sylow.exists_comap_subtype_eq` already gives the reverse
existence direction needed in part (c), but does not package the full normal
restriction or the cardinal-divisibility theorem.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b01J01.md`

## Follow-up Needed

- formalize parts (b)--(d) using finite abelian group and Sylow action APIs

# Proof Outline: t94J04

The index-one case is closed by `apm_t94J04_subgroups_equiv_of_index_one`:
both subgroups are top and hence canonically isomorphic. The main theorem now
actually splits on `k = 1` and invokes this lemma, so its remaining sorry is
confined to `k ≠ 1`.

For positive general index, realize each subgroup as the fundamental group of
a connected `k`-sheeted covering surface.  The cover is closed and orientable,
and its Euler characteristic is `k * (-2)`, so its genus is `k+1`.  Surface
classification then identifies the two covering spaces and their fundamental
groups.

The numerical step is compiled as
`apm_t94J04_eulerChar_cover_arithmetic`:
`2 - 2(k+1) = k(2 - 2·2)` over the integers.

## Remaining boundary

Mathlib does not package the subgroup--cover correspondence, finite-cover
Euler-characteristic multiplicativity, or classification of closed orientable
surfaces.  The encoded homology signature must also be connected to the
genus-two surface type before those arguments apply.

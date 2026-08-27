# Singular excision

## Public range-subcomplex inclusion interface

The Mayer--Vietoris transport uses the following public simplicial maps:

- `subcomplexIntersectionToLeft` and `subcomplexIntersectionToRight`;
- `subcomplexLeftToUnion` and `subcomplexRightToUnion`;
- `ambientSubspaceRange` and `ambientSubspaceRangeInclusion`;
- `topologicalSubspaceInclusion` for the corresponding actual subspace map.

`ambientSubspaceRangeChainsIso` identifies chains on the ambient range with
the production singular chains of the subspace. The simplicial, chain, and
homology comparison squares are respectively
`ambientSubspaceRangeInclusion_square`,
`ambientSubspaceRangeChainsIso_naturality`, and
`ambientSubspaceRangeHomologyIso_naturality`. The four named chain-level
specializations cover intersection-to-left, intersection-to-right,
left-to-union, and right-to-union.

These results do not assert Mayer--Vietoris exactness for production singular
homology. For an open two-member cover, the remaining comparison is between
the join of the two ambient range subcomplexes (the cover-small complex) and
all singular chains on the union. This comparison is a homology isomorphism,
not a literal equality of chain complexes; the production adapter must use
`coverSmall` naturality when conjugating the reassembly arrow.

That memberwise naturality is now compiled as
`coverMemberRangeInclusion_square`,
`coverMemberRangeChainsIso_naturality`, and
`coverMemberRangeHomologyIso_naturality`. Each says that passing from one
range subcomplex into `coverSmall` and then into ambient singular chains is
the actual subspace inclusion. The remaining adapter work is categorical:
assemble the two memberwise squares through the biproduct comparison for the
homology functor and transport the intersection along
`ambientSubspaceRange_inf`.

# Generic target-natural source reconstruction

This target reconstructs a source-category equivalence from a family

```lean
(A ⥤ C) ≌ (B ⥤ C)
```

that is natural under postcomposition in `C`. The forward candidate is the
inverse image of `𝟭 B`, while the inverse candidate is the forward image of
`𝟭 A`. The forward round trip is compared after applying the forward mapping
equivalence; the reverse round trip uses `CatCommSq.vInv` and compares after
applying its inverse. Both comparisons return to the source through
`Functor.preimageIso`, and `CategoryTheory.Equivalence.mk` packages the result.
The functor and inverse normalization theorems expose the two candidates
definitionally.

For the torus-circle point wedge, the mapping-category family gives
`wedgeSourceEquivalence` from the actual fundamental groupoid to the
single-object category of

```lean
Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ).
```

`wedgeBase` is the quotient image of the torus basepoint. Its functor image is
explicitly identified with the unique `SingleObj` object.
`wedgeFundamentalGroupMulEquiv` is oriented from the source fundamental group
to the torus-first/circle-second free product. It is the fully faithful
endomorphism equivalence, followed by conjugation along the displayed object
equality, followed by `SingleObj.toEnd.symm`.

The normalization stops at the base-object equality and this abstract
endomorphism-group equivalence. This target does not prove how particular
torus or circle loop generators map, provide a frozen adapter, establish
`bridge_2`, or claim closure of a downstream problem.

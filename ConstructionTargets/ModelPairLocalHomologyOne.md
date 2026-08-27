# One-dimensional model-pair local homology

`ModelPairLocalHomologyOne.lean` computes the degree-one relative singular
homology of the open Euclidean one-disk relative to the complement of its
origin:

```text
H₁(B¹, B¹ ∖ {0}; ℤ) ≅ ℤ.
```

The construction uses only already compiled infrastructure:

1. `closedDiskPair_to_openDiskPair_homologyMap_isIso_one` compares the closed
   one-disk/boundary pair with the open one-disk/puncture pair.
2. `closedDiskOneRelativeIsoInterval` identifies the closed-disk pair with
   the unit interval relative to its endpoints.
3. `intervalBoundaryRelativeH1IsoInt` supplies the computed integral class.

The resulting `openDiskOnePunctureRelativeH1Generator` maps to `1` and is
proved nonzero.  `radialPairMap_closedGenerator` additionally states that the
actual relative homology map induced by radial shrinking carries the oriented
closed-disk class to this local generator.  It is therefore a concrete local
orientation class, not an assumed manifold fundamental class.

## Boundary

This target does not construct the localization map from the top homology of
an arbitrary manifold to its local homology.  The next generic interface is a
chart-pair transport theorem followed by compatibility of a global oriented
fundamental class with this local generator.  Neither localization monicity
nor that compatibility follows merely from this model calculation.

# Relative singular connecting-map naturality

This target supplies the connecting-map square for actual continuous maps of
pairs, and uses it to reduce a one-dimensional local-generator computation to
the induced map on the puncture's degree-zero homology. Chains and homology
use the production integral singular representation in `AddCommGrpCat`.

## Construction and declarations

For subsets `A ⊆ X`, `B ⊆ Y`, a continuous map `f : X → Y`, and
`hf : Set.MapsTo f A B`, `singularPairConnecting_naturality` proves

```text
δ_A ≫ H_n(f restricted to A) = H_{n+1}(f on the relative pair) ≫ δ_B.
```

Its proof constructs a morphism from `singularPairShortComplex A` to
`singularPairShortComplex B`. The three components are the singular chain map
of `subspaceMap A B f hf`, the ambient singular chain map of `f`, and
`relativeSingularMap A B f hf`. The two squares are supplied by
`singularSubspaceMap_naturality` and
`relativeSingularMap_projection_naturality`; connecting-map naturality then
follows from `HomologicalComplex.HomologySequence.δ_naturality` applied to the
production short exact sequences. This theorem holds for every `n : ℕ`.

The remaining three declarations specialize to the open one-disk `D` and its
puncture `P = D ∖ {0}`, with the existing chosen class
`g = openDiskOnePunctureRelativeH1Generator`:

- `modelGenerator_boundary_map` proves `δ(H₁(f)(g)) = H₀(f|P)(δ(g))`.
- `modelConnecting_injective` proves that `δ : H₁(D,P; ℤ) → H₀(P; ℤ)` is
  injective, using contractibility of `D`, vanishing of its absolute `H₁`,
  and exactness of the pair sequence.
- `modelGenerator_map_eq_iff_boundary` combines these facts. For every
  continuous self-map `f` of `D` carrying `P` into itself and every
  `z : H₁(D,P; ℤ)`, it proves

  ```text
  H₁(f)(g) = z  ↔  H₀(f|P)(δ(g)) = δ(z).
  ```

No homeomorphism or induced-map sign is assumed in this equivalence.

## Evidence and consumers

The Lean file is a byte-for-byte promotion of
`/tmp/RelativeSingularConnectingNaturalityProbe.lean`, SHA-256
`64cf111d7cb682142264242e13436250be389e6f17c1bd891b61d089fceb9b61`.
It retains all four `#print axioms` checks; each declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`.

The observed consumer in this packet is the concrete model equivalence above.
The named next consumer is `euclidean-one-disk-local-orientation`;
`circle-oriented-chart-transition` is a proposed later consumer. The import
uses `ChartPairRelativeHomologyTransport` and its existing model-pair and
production pair-map dependencies. No frozen problem is changed and the
placeholder delta is zero.

## Remaining boundary

Compute `δ(g)` in puncture-component coordinates, then prove that the actual
`H₀` action fixes or exchanges those components under increasing or decreasing
pointed coordinate homeomorphisms. Generator characterization and the full
model sign theorem remain in the parent probe. This packet proves neither
geometric orientation compatibility nor a model computation in arbitrary
dimensions. Restricted manifold charts, overlap compatibility, global
fundamental classes, and localization monicity remain separate constructions.

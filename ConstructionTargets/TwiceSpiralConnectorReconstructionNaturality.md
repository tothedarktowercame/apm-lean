# Naturality of connector reconstruction

`reconstructionIso_left_naturality` and
`reconstructionIso_right_naturality` keep the chosen base connectors explicit.
Each is exactly the corresponding piece natural transformation's naturality
equation at that connector.

`reconstructionIso_naturality` combines the two component equations with
coordinate-pseudococone morphism extensionality.
`reconstructionNatIso` therefore packages
`extractionFunctor ⋙ reconstructionFunctor ≅ 𝟭`.

The remaining round trip is on `VertexData`.  A connector from a prescribed
base to itself need not be the identity, so extracting a reconstructed
constant functor conjugates its vertex action by the represented base
connector.  The next packet must build that conjugating vertex-data
isomorphism and prove its glue compatibility; no categorical equivalence is
claimed here.

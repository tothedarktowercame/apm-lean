# Twice-spiral connector vertex extraction

`vertexDataHom` evaluates a coordinate pseudococone morphism at the prescribed
left and right connector bases.  Naturality at each base loop proves the two
vertex-representation intertwining equations.  Evaluating
`CoordinatePseudoCoconeHom.glue_naturality` at the boundary connector base
proves the base-glue square.

`extractionFunctor` packages this construction as a functor from coordinate
pseudococones to `VertexData`.  Its object and morphism component formulas are
exported as simp lemmas.

The next seam is the extraction/reconstruction comparison.  Its piece
components must use the chosen connector isomorphisms, and their overlap glue
square must retain the leg-compatibility equations; no equivalence is claimed
in this packet.

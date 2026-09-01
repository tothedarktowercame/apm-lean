# Torus-circle wedge fundamental-groupoid span cells

This target specializes the generic span-pseudococone transport API to the
literal torus-circle wedge open cover from
`ConstructionTargets.TorusCircleWedgeOpenCover`. The actual span legs are the
fundamental-groupoid functors induced by the overlap inclusions into `U` and
`V`.

The coordinate span uses the constant maps from `Unit` to the selected bases
`((1, 1) : Torus)` and `(1 : Circle)`. The overlap basepoint is the literal
left representative of the wedge base, and `UVHomotopyEquiv_invFun_unit`
proves that the reviewed overlap contraction sends `()` to that exact subtype
point.

`left_coordinate_map_strict` and `right_coordinate_map_strict` retain the
literal representative calculations through `UVHomotopyEquiv.invFun`,
`UModel_left`, and `VModel_left`, rather than replacing them with abstract
contractibility. Their reflexive homotopies induce the comparison cells
`αL` and `αR` in the required orientation

```lean
eK.inverse ⋙ actual ⋙ ePiece.functor ≅ coordinateLeg
```

where `eK`, `eL`, and `eR` are the reviewed fundamental-groupoid equivalences
coming from `UVHomotopyEquiv`, `UHomotopyEquiv`, and `VHomotopyEquiv`.

`coordinatePseudoCoconeEquivalence` is the concrete specialization of
`pseudoCoconeEquivalenceOfSpanEquivalences`, and
`coordinatePseudoCoconePostcomposeIso` is its arbitrary-target postcomposition
naturality wrapper. The object normalization formulas
`eK_inverse_unit_obj`, `left_leg_base_obj`, and `right_leg_base_obj` expose
the exact overlap, left-piece, and right-piece selected bases needed for later
free-product and frozen-facing adapters.

This file stops at the concrete span cells and their arbitrary-target
naturality. It does not add representability, source reconstruction, frozen
adapters, or any problem-facing closure.

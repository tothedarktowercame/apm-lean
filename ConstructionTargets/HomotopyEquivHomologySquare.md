# HomotopyEquivHomologySquare

This target packages the naturality calculation needed whenever source and
target spaces are replaced by explicit homotopy-equivalent coordinate models.

For a strict conjugated equality `eB.toFun ∘ f ∘ eA.invFun = g`,
`conjugated_homologyMap_of_strict_square` proves that the map induced by `f`,
conjugated through the singular-homology isomorphisms induced by `eA` and
`eB`, is the map induced by `g`.

The result is generic in the spaces and degree.  It assumes neither a
Mayer--Vietoris arrow comparison nor any calculation of the resulting
homology objects.

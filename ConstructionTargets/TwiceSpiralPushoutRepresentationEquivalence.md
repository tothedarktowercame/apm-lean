# Twice-spiral pushout representations

This target transports morphisms between integer-coordinate vertex data and
representations of the literal `Monoid.PushoutI` object.  The left component
intertwines the transported right action using the coordinate glue square;
conjugation turns those equations into monoid-homomorphism equalities, and
`Monoid.PushoutI.hom_ext_nonempty` extends them from both `of` legs to every
pushout element.

The reverse morphism uses the same arrow on both pieces.  These constructions
are packaged as `coordinateToPushoutFunctor` and
`pushoutToCoordinateFunctor`.

The next exact seam is the objectwise round trips.  On the coordinate side the
comparison has left component identity and right component the original
`baseGlue`; on the pushout side the recovered lifted action must first be
identified with the original action by `PushoutI.hom_ext_nonempty`.  Their
naturality and triangle identity remain to be packaged, so this packet does
not claim an equivalence or an ambient fundamental-group isomorphism.

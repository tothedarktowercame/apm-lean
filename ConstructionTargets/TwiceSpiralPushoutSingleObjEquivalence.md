# Pushout representations as single-object functors

`representationToFunctor` uses `SingleObj.functor`, and its morphism map uses
`SingleObj.natTrans`.  Conversely, `functorAction` evaluates a functor at the
unique object and turns its endomorphism map into a monoid homomorphism.  Its
multiplication proof explicitly combines `SingleObj.comp_as_mul` with the
reversed multiplication convention of `End`.

The two identity-component round trips and their naturality equations package
`pushoutRepresentationSingleObjEquivalence`.  Composing this with the compiled
gluing-to-pushout-representation equivalence yields
`gluingFundamentalGroupoidSingleObjMappingEquivalence`.

This is an equivalence of mapping categories for the fixed target groupoid
`C`; it does not assert an equivalence of source groupoids or an ambient
fundamental-group isomorphism.

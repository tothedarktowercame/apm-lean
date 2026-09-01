# Free-product representations as single-object functors

This target identifies `FreeProductRepresentation G H C` with the functor
category `SingleObj (Monoid.Coprod G H) ⥤ C`.

`representationToFunctor` bundles a representation action with
`SingleObj.functor`; its map sends an intertwiner to the corresponding natural
transformation. `functorToRepresentation` extracts the target object and the
monoid action `x ↦ F.map x`. The multiplication proof explicitly reconciles
`End.mul_def` with `SingleObj.comp_as_mul`, preserving the coproduct factor and
composition orientation.

Both round trips have identity components. Their natural isomorphisms and the
compiled triangle produce `representationSingleObjEquivalence`, oriented from
free-product representations to single-object functors.

The forward and inverse constructions commute with target postcomposition up
to `representationToFunctorPostcomposeIso` and
`functorToRepresentationPostcomposeIso`. The inverse comparison uses the
explicit dependent equality `inverse_postcompose_action_eq`; its component is
identity on the target and transports the action equality pointwise.

The normalization lemmas expose representation actions as functor maps,
functor maps as extracted actions, representation morphisms as components at
the unique object, and identity components for both postcomposition
comparisons. This target contains no torus specialization, connector, source
reconstruction, or frozen-problem uptake.

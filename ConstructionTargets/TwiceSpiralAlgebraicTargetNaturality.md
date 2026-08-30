# Twice-spiral algebraic target naturality

`TwiceSpiralAlgebraicTargetNaturality.lean` composes the already proved target
postcomposition comparisons along the algebraic chain

```text
VertexData
  -> CoordinateVertexData
  -> PushoutRepresentation
  -> (SingleObj (TwiceSpiralPushout d) ⟶ C).
```

The left-associated `vertexToSingleObjEquivalence` is the object-level
equivalence.  The three component `CatCommSq`s use, respectively,
`toCoordinatePostcomposeIso`, `coordinateToPushoutPostcomposeIso`, and
`representationToFunctorPostcomposeIso`.  Consequently their composite keeps
the coordinate conjugation calculation, `Monoid.PushoutI.hom_ext_nonempty`
argument, mapped `baseGlue`, and `SingleObj` composition convention in the
focused proofs where they were established.

`vertexSingleObjSquare` has the forward orientation

```text
postcomposeVertexDataFunctor ⋙ vertexToSingleObj(D).functor
  ≅ vertexToSingleObj(C).functor ⋙ postcomposeSingleObj(H).
```

`singleObjVertexMate`, constructed with `CatCommSq.vInv`, has the inverse
orientation

```text
postcomposeSingleObj(H) ⋙ vertexToSingleObj(D).inverse
  ≅ vertexToSingleObj(C).inverse ⋙ postcomposeVertexDataFunctor.
```

The file also exports the inverse mates for the coordinate/pushout and
pushout/single-object component squares.  It stops at this algebraic
composition: no connector or geometric square is pasted onto it here.

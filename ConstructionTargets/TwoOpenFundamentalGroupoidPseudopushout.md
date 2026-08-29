# Two-open fundamental-groupoid pseudopushout

`twoOpenFundamentalGroupoidPseudopushoutEquivalence` composes the compiled
ambient-functor/descent equivalence with the compiled
descent/pseudococone equivalence. For open `U` and `V` covering `X`, it gives

```text
(FundamentalGroupoid X ⟶ C) ≌ PseudoFunctorCocone U V C.
```

The four object/map lemmas expose that its forward functor restricts an
ambient functor and natural transformation along the actual left and right
subtype inclusions. The overlap comparison is the canonical isomorphism
carried by `descentOverlapIso`; the previously proved descent naturality is
what makes it a pseudococone.

`twoOpenFundamentalGroupoid_pseudopushout_mapping_property` records the same
equivalence as a named proposition quantified over an arbitrary target
category. This is a bicategorical/pseudococone mapping property. It does not
claim that the ambient groupoid is an ordinary `Limits.Pushout`, whose cocones
would require strict equality of the two overlap composites.

For the twice-spiral solid-torus gluing, the next specialization is to choose
the collared two-open cover and evaluate this equivalence on one-object target
groupoids. One must then identify the induced piece and overlap functors with
the already compiled boundary/solid-torus fundamental-group coordinates; that
is the remaining topological-to-algebraic comparison before applying the
banked `ZMod 2` group-pushout calculation.

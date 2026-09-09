# Lower-dimensional image nullity with a surjective lift

`image_zero_of_lower_dimension_surjective_lift` proves that `f '' s` has zero
additive Haar measure when the finite-dimensional real normed source has
strictly smaller finrank than the Borel target, `f` is ambient differentiable
at every point of the arbitrary set `s`, and a surjective continuous linear
map `p` from the target to the source is supplied.

The proof lifts `f` to the self-map `f ∘ p`. The chain rule and the strict
dimension inequality make its derivative nonsurjective throughout the
preimage of `s`. The reviewed `sameSpace_ambient_criticalImage_zero` gives
nullity of the lifted critical image. Surjectivity of `p` puts the entire
original image inside that null set.

No measurable structure or measure on the source, measurability or openness
of `s`, continuity of the derivative, or image-nullity certificate is assumed.
The surjective continuous linear map remains an explicit premise; this module
does not construct it internally.

The Lean file is identical to the accepted fixture
`/tmp/SardLowerDimensionSurjectiveLiftNullityProbe.lean`, SHA-256
`c577e819b035b85cc2015b893d656ef4467446ed6270434fad0a149b1840566e`.
Its axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

For t93A04 and potential consumers t01A08, t01J04, t92J07, and t96J05,
internal construction of the surjective map, low-order assembly, and the
complementary-overlap analytic premise remain. This is not full rectangular
or manifold Morse–Sard closure. The frozen consumer and ledger are unchanged.

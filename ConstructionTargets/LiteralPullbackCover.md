# Literal pullback coverings

`LiteralPullbackCover.lean` constructs covering base change for arbitrary
topological spaces `E`, `B` and `Y`. Given `p : E → B` and `f : Y → B`,
`Pullback p f` is the literal subtype `{q : Y × E // f q.1 = p q.2}`
with the induced topology; `projection p f` sends a point to its `Y` coordinate.

For a continuous `f`, `evenlyCovered` pulls an actual evenly covered
neighborhood `U` of `f y` back to `f ⁻¹' U`. If the original trivialization
is `H`, the constructed trivialization sends `(y,e)` to `(y,(H e).2)`.
Its inverse uses the `E` coordinate of `H.symm (f y,i)`. Both inverse
identities, continuity, and the equation over the base are proved explicitly.
`isCoveringMap` applies this construction to the neighborhoods supplied by
the original covering. Neither a covering structure on the pullback nor a
globally uniform sheet type is assumed.

`fiberHomeomorph` identifies the projection fiber over `y` with
`{e : E // p e = f y}`. Its evaluation is exactly the `E` coordinate;
the inverse sends `e` to `(y,e)`. This homeomorphism does not require
continuity of `f` or a covering hypothesis. `fiber_card` proves equality of
`Nat.card`, and `sheet_card` transports any specified cardinality `n`.
For finite fibers these are the exact finite sheet counts; the construction
also permits empty fibers.

The examples include the real-to-`AddCircle 1` covering pulled back along
doubling and an empty covering pulled back to the disconnected `Bool` base.
The latter has zero-cardinality fibers at every base point.

The source is an exact promotion of `/tmp/LiteralPullbackCover.lean`, SHA256
`c4bcc90c9abaaaf871835c9f6eb6b2dcf4feffe7215d96b4d8d50e695015772e`.
Validation comprises fixture and canonical compilation, the focused Lake
build, nine printed axiom audits allowing only `propext`, `Classical.choice`
and `Quot.sound`, and placeholder, forbidden-declaration and scope checks.

This packet establishes literal base change and fiber transport only.
Frozen consumer assembly, wedge-point covering gluing, universal-cover
construction, deck classification and nonhomeomorphism of total spaces
remain separate obligations. No frozen consumer closure is claimed.

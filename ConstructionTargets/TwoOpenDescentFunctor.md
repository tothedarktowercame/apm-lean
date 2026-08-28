# Two-open descent functor

`twoOpenDescentFunctor` packages the descended path-class assignment as an
actual functor from `FundamentalGroupoid X` to the target category. Its object
map is `D.obj`; its morphism map is `quotientEvaluation`. The functor laws use
the proved `quotientEvaluation_refl` and `quotientEvaluation_trans` equations.

`twoOpenDescentFunctor_map_mk` identifies the image of any represented path
with `D.evaluate S` for every supplied subordinate subdivision certificate.

Restriction comparison with the original `U` and `V` functors remains a
separate packet: it requires choosing the one-piece subdivision and spelling
out the subtype/object `eqToHom` coordinates. No pushout universal property is
claimed here.

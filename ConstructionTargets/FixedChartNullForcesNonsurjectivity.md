# Fixed-chart nullity forces nonsurjectivity

This target proves the final coordinate-local contradiction needed by the
dimension-gap program.  For one fixed point `q` in a boundaryless target
manifold, suppose the part of `range f` lying in `extChartAt I q` has null
coordinate image under an explicit additive Haar measure.  If `f` were
surjective, that coordinate image would be the entire extended-chart target.
The target is open because the model is boundaryless, nonempty because it
contains the coordinate of `q`, and therefore has positive measure.

The theorem does not place a measure on the manifold, compare different
charts, or prove the required coordinate nullity.  It assumes no smoothness
of `f`; smoothness belongs solely to the upstream chartwise-nullity producer.
The explicit `Boundaryless` requirement is essential here: arbitrary corner
chart targets need not be open in the full model space, so the same positivity
argument is unavailable without a relative measure theorem.

The hypothesis is deliberately the literal measure equation rather than the
earlier `ChartCoordinateNull` wrapper.  In the canonical Mathlib revision,
`extChartAt` is a `PartialEquiv`, whereas that wrapper was parameterized by an
`OpenPartialHomeomorph`; the literal equation is the common, type-correct
interface and loses no mathematical content needed by this theorem.

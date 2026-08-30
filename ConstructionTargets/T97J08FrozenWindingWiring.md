# T97J08 frozen winding wiring

This target matches the topological winding predicate in frozen `t97J08`.
It turns the normalized nonzero complex loop into `Circle`, applies the
periodic lift construction, and coerces the resulting circle homotopy back to
complex values.

For uniqueness, an arbitrary frozen complex homotopy is restricted to the
unit square and bundled into `Circle`.  Its lifted bottom edge is compared to
the canonical global lift, and its lifted top edge is compared to the linear
lift `m * 2π * u`.  Each comparison is constant because its circle
exponential is constant.  Homotopy invariance of endpoint displacement then
forces the two integers to agree.

No beta-form integral or integral winding formula is used.  The remaining
frozen theorem work is therefore the separate analytic identification of the
beta integral with this unique topological integer.

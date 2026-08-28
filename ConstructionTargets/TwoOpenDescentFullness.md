# Two-open descent 2-cell existence data

`CompatibleNatTrans D E` packages natural transformations between the two
piece functors of two descent data.  Components are compared only after the
explicit `D.obj_eq` and `E.obj_eq` transports into the common ambient object
coordinates.  The structure records agreement on overlap objects and on both
sides of every overlap-path naturality square.

`ambientApp` chooses a containing chart for an ambient point.
`ambientApp_eq_true` and `ambientApp_eq_false` prove that either supplied chart
gives the same component, with the overlap case discharged by
`overlap_app`. `ambientComponent_eq_chart` identifies the resulting candidate
ambient component with each transported piece component after restriction.

The remaining theorem is naturality of `ambientComponent` for an arbitrary
ambient path class.  Its proof must expand a subordinate subdivision, apply
the naturality of the selected piece transformation to every segment, and
telescope those squares through `TwoOpenDescentDatum.composeFin`.  Until that
finite-composite theorem is supplied, this target does not construct or assume
an ambient natural transformation and does not state a pushout property.

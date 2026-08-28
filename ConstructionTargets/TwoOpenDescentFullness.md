# Two-open descent 2-cell existence data

`CompatibleNatTrans D E` packages natural transformations between the two
piece functors of two descent data. Components are compared only after the
explicit `D.obj_eq` and `E.obj_eq` transports into the common ambient object
coordinates. Agreement on overlap objects is the only compatibility field;
the previously separate overlap-path equations follow from piece naturality
and are not part of the interface.

`ambientApp` chooses a containing chart for an ambient point.
`ambientApp_eq_true` and `ambientApp_eq_false` prove that either supplied chart
gives the same component, with the overlap case discharged by
`overlap_app`. `ambientComponent_eq_chart` identifies the resulting candidate
ambient component with each transported piece component after restriction.

`mappedPiece_naturality` transports each piece naturality square into common
coordinates. `composeFin_naturality` telescopes these squares across an
arbitrary subordinate subdivision. `evaluate_naturality` includes the path
endpoint transports, and `ambientNatTrans` descends the result to arbitrary
fundamental-groupoid morphisms. `ambientNatTrans_restriction_app` proves that
its restriction agrees with each supplied piece transformation through the
banked restriction isomorphisms.

Together with the separate uniqueness theorem, this closes the 2-cell
fullness/faithfulness layer. This target does not package a `Limits.Pushout`:
the remaining interface is the object-level cocone and equivalence between
compatible descent data and ambient functors, including the required
pseudonatural restriction isomorphisms.

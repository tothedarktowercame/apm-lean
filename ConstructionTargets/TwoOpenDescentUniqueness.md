# Two-open descent uniqueness

This target proves the faithful, or uniqueness-of-natural-transformations,
part of the two-open fundamental-groupoid descent interface.

`natTrans_ext_of_twoOpen_restrictions` says that two natural transformations
between ambient fundamental-groupoid functors are equal when their whiskered
restrictions along both cover-piece inclusions are equal.  The companion
`natTrans_ext_of_twoOpen_app` accepts the corresponding component equations.
The proof uses the cover equation to place each ambient object in one of the
two pieces.  No strict equality between functors with merely isomorphic object
coordinates is asserted.

The remaining universal-property work is the fullness/existence direction:
given compatible transformations between the two restricted functors, build
an ambient natural transformation and prove its naturality on an arbitrary
represented path.  That proof must use subordinate subdivisions,
`evaluate_eq_of_subdivisions`, and the restriction isomorphisms.  Only after
that construction is available is it honest to package a categorical pushout
or an equivalence of functor categories.

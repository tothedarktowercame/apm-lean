# CircleUniversalCover

This target packages Mathlib's existing quotient cover
`Real → AddCircle (2 * pi)` through `AddCircle.homeomorphCircle'`.

It proves that `Circle.exp` is a covering map and a local homeomorphism,
identifies each fiber by integral multiples of `2 * pi`, constructs Mathlib's
canonical continuous lift of a based loop starting at zero, and proves that a lifted
loop's endpoint is a unique integral period.

This is not yet a computation of `FundamentalGroup Circle 1`.  The remaining
step is to prove that the endpoint integer is invariant under based homotopy,
that every integer occurs, and that loop concatenation adds endpoint integers.
Those require a based covering-homotopy/endpoint argument; none is assumed
here.

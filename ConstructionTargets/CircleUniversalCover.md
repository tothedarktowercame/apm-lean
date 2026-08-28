# CircleUniversalCover

This target packages Mathlib's existing quotient cover
`Real → AddCircle (2 * pi)` through `AddCircle.homeomorphCircle'`.

It proves that `Circle.exp` is a covering map and a local homeomorphism,
identifies each fiber by integral multiples of `2 * pi`, constructs Mathlib's
canonical continuous lift of a based loop starting at zero, and proves that a lifted
loop's endpoint is a unique integral period.  The chosen integer coordinate is
proved invariant under homotopies relative to the two endpoints, using
Mathlib's covering homotopy lifting theorem.

This is not yet a computation of `FundamentalGroup Circle 1`.  The remaining
step is to prove that every integer occurs and that loop concatenation adds
endpoint integers.  No winding classification or fundamental-group quotient
construction is assumed here.
